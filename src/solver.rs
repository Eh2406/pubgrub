// SPDX-License-Identifier: MPL-2.0

//! PubGrub version solving algorithm.
//!
//! It consists in efficiently finding a set of packages and versions
//! that satisfy all the constraints of a given project dependencies.
//! In addition, when that is not possible,
//! PubGrub tries to provide a very human-readable and clear
//! explanation as to why that failed.
//! Below is an example of explanation present in
//! the introductory blog post about PubGrub
//!
//! ```txt
//! Because dropdown >=2.0.0 depends on icons >=2.0.0 and
//!   root depends on icons <2.0.0, dropdown >=2.0.0 is forbidden.
//!
//! And because menu >=1.1.0 depends on dropdown >=2.0.0,
//!   menu >=1.1.0 is forbidden.
//!
//! And because menu <1.1.0 depends on dropdown >=1.0.0 <2.0.0
//!   which depends on intl <4.0.0, every version of menu
//!   requires intl <4.0.0.
//!
//! So, because root depends on both menu >=1.0.0 and intl >=5.0.0,
//!   version solving failed.
//! ```
//!
//! The algorithm is generic and works for any type of dependency system
//! as long as packages (P) and versions (V) implement
//! the [Package] and Version traits.
//! [Package] is strictly equivalent and automatically generated
//! for any type that implement [Clone] + [Eq] + [Hash] + [Debug] + [Display].
//!
//! ## API
//!
//! ```
//! # use std::convert::Infallible;
//! # use pubgrub::solver::{resolve, OfflineDependencyProvider};
//! # use pubgrub::error::PubGrubError;
//! # use pubgrub::range::Range;
//! #
//! # type NumVS = Range<u32>;
//! #
//! # fn try_main() -> Result<(), PubGrubError<OfflineDependencyProvider::<&'static str, NumVS>>> {
//! #     let dependency_provider = OfflineDependencyProvider::<&str, NumVS>::new();
//! #     let package = "root";
//! #     let version = 1u32;
//! let solution = resolve(&dependency_provider, package, version)?;
//! #     Ok(())
//! # }
//! # fn main() {
//! #     assert!(matches!(try_main(), Err(PubGrubError::NoSolution(_))));
//! # }
//! ```
//!
//! Where `dependency_provider` supplies the list of available packages and versions,
//! as well as the dependencies of every available package
//! by implementing the [DependencyProvider] trait.
//! The call to [resolve] for a given package at a given version
//! will compute the set of packages and versions needed
//! to satisfy the dependencies of that package and version pair.
//! If there is no solution, the reason will be provided as clear as possible.

use std::cmp::Reverse;
use std::collections::{BTreeMap, BTreeSet as Set};
use std::convert::Infallible;
use std::error::Error;
use std::fmt::{Debug, Display};

use crate::error::PubGrubError;
use crate::internal::core::State;
use crate::internal::incompatibility::Incompatibility;
use crate::package::Package;
use crate::type_aliases::{Map, SelectedDependencies};
use crate::version_set::VersionSet;
use log::{debug, info};

/// Main function of the library.
/// Finds a set of packages satisfying dependency bounds for a given package + version pair.
pub fn resolve<DP: DependencyProvider>(
    dependency_provider: &DP,
    package: DP::P,
    version: impl Into<DP::V>,
) -> Result<SelectedDependencies<DP>, PubGrubError<DP>> {
    let mut state: State<DP> = State::init(package.clone(), version.into());
    let mut added_dependencies: Map<DP::P, Set<DP::V>> = Map::default();
    let mut next = package;
    loop {
        dependency_provider
            .should_cancel()
            .map_err(PubGrubError::ErrorInShouldCancel)?;

        info!("unit_propagation: {}", &next);
        state.unit_propagation(next)?;

        debug!(
            "Partial solution after unit propagation: {}",
            state.partial_solution
        );

        let Some(highest_priority_pkg) = state
            .partial_solution
            .pick_highest_priority_pkg(|p, r| dependency_provider.prioritize(p, r))
        else {
            return Ok(state.partial_solution.extract_solution());
        };
        next = highest_priority_pkg;

        let term_intersection = state
            .partial_solution
            .term_intersection_for_package(&next)
            .ok_or_else(|| {
                PubGrubError::Failure("a package was chosen but we don't have a term.".into())
            })?;
        let decision = dependency_provider
            .choose_version(&next, term_intersection.unwrap_positive())
            .map_err(PubGrubError::ErrorChoosingPackageVersion)?;
        info!("DP chose: {} @ {:?}", next, decision);

        // Pick the next compatible version.
        let v = match decision {
            None => {
                let inc = Incompatibility::no_versions(next.clone(), term_intersection.clone());
                state.add_incompatibility(inc);
                continue;
            }
            Some(x) => x,
        };

        if !term_intersection.contains(&v) {
            return Err(PubGrubError::Failure(
                "choose_package_version picked an incompatible version".into(),
            ));
        }

        let is_new_dependency = added_dependencies
            .entry(next.clone())
            .or_default()
            .insert(v.clone());

        if is_new_dependency {
            // Retrieve that package dependencies.
            let p = &next;
            let start_range = state.incompatibility_store.start_range();

            let mut dependency_adder = DependencyAdder {
                state: &mut state,
                package: p,
                version: &v,
                err: None,
            };
            dependency_provider
                .get_dependencies(p, &v, &mut dependency_adder)
                .map_err(|err| PubGrubError::ErrorRetrievingDependencies {
                    package: p.clone(),
                    version: v.clone(),
                    source: err,
                })?;

            if let Some(err) = dependency_adder.err {
                return Err(err);
            }

            let dep_incompats = state.incompatibility_store.make_range(start_range);

            state.partial_solution.add_version(
                p.clone(),
                v,
                dep_incompats,
                &state.incompatibility_store,
            );
        } else {
            // `dep_incompats` are already in `incompatibilities` so we know there are not satisfied
            // terms and can add the decision directly.
            info!("add_decision (not first time): {} @ {}", &next, v);
            state.partial_solution.add_decision(next.clone(), v);
        }
    }
}

// Maybe this trait should actually be made sealed.
pub trait DependencyVisitor<P, VS: VersionSet, M> {
    fn add_dependency(&mut self, dependency: P, requerment: VS);

    fn make_unavailable_reason(&mut self, reason: M);

    fn make_unavailable(&mut self)
    where
        M: Default,
    {
        self.make_unavailable_reason(M::default());
    }

    fn add_iter_dependencies(&mut self, deps: impl IntoIterator<Item = (P, VS)>) {
        for dep in deps {
            self.add_dependency(dep.0, dep.1);
        }
    }

    // Notice that we could add other kinds of dependency edges here without breaking compatibility.
}

struct DependencyAdder<'c, DP: DependencyProvider> {
    state: &'c mut State<DP>,
    package: &'c DP::P,
    version: &'c DP::V,
    err: Option<PubGrubError<DP>>,
}
impl<'c, DP: DependencyProvider> DependencyVisitor<DP::P, DP::VS, DP::M>
    for DependencyAdder<'c, DP>
{
    fn add_dependency(&mut self, dependency: DP::P, requerment: DP::VS) {
        if self.package == &dependency {
            self.err = Some(PubGrubError::SelfDependency {
                package: self.package.clone(),
                version: self.version.clone(),
            });
            return;
        }

        self.state.add_incompatibility_from_dependency(
            self.package.clone(),
            self.version.clone(),
            dependency,
            requerment,
        );
    }

    fn make_unavailable_reason(&mut self, reason: DP::M) {
        self.state
            .add_incompatibility(Incompatibility::custom_version(
                self.package.clone(),
                self.version.clone(),
                reason,
            ));
    }
}

/// This implementation is only useful if you want to introspect what a call to `get_dependencies`
/// did (for testing) or store what a call to `get_dependencies` did for replaying later (for caching).
pub struct DependencyCollector<DP: DependencyProvider> {
    #[allow(clippy::type_complexity)]
    state: Result<Vec<(DP::P, DP::VS)>, DP::M>,
}

impl<DP: DependencyProvider> Default for DependencyCollector<DP> {
    fn default() -> Self {
        Self::new()
    }
}

impl<DP: DependencyProvider> DependencyCollector<DP> {
    pub fn new() -> Self {
        Self {
            state: Ok(Vec::new()),
        }
    }
    /// Returns a list of all normal dependencies added or the reason if it was ever made unavailable.
    #[allow(clippy::type_complexity)]
    pub fn collect(self) -> Result<Vec<(DP::P, DP::VS)>, DP::M> {
        self.state
    }
    pub fn replay<DV: DependencyVisitor<DP::P, DP::VS, DP::M>>(&self, other: &mut DV) {
        match self.state.as_ref() {
            Ok(deps) => {
                for (dep, range) in deps {
                    other.add_dependency(dep.clone(), range.clone());
                }
            }
            Err(reason) => other.make_unavailable_reason(reason.clone()),
        }
    }
}

impl<DP: DependencyProvider> DependencyVisitor<DP::P, DP::VS, DP::M> for DependencyCollector<DP> {
    fn add_dependency(&mut self, dependency: DP::P, requerment: DP::VS) {
        let Ok(state) = &mut self.state else {
            return;
        };
        state.push((dependency, requerment));
    }

    fn make_unavailable_reason(&mut self, reason: DP::M) {
        self.state = Err(reason);
    }
}

/// Trait that allows the algorithm to retrieve available packages and their dependencies.
/// An implementor needs to be supplied to the [resolve] function.
pub trait DependencyProvider {
    /// How this provider stores the name of the packages.
    type P: Package;

    /// How this provider stores the versions of the packages.
    ///
    /// A common choice is [`SemanticVersion`][crate::version::SemanticVersion].
    type V: Debug + Display + Clone + Ord;

    /// How this provider stores the version requirements for the packages.
    /// The requirements must be able to process the same kind of version as this dependency provider.
    ///
    /// A common choice is [`Range`][crate::range::Range].
    type VS: VersionSet<V = Self::V>;

    /// Type for custom incompatibilities.
    ///
    /// There are reasons in user code outside pubgrub that can cause packages or versions
    /// to be unavailable. Examples:
    /// * The version would require building the package, but builds are disabled.
    /// * The package is not available in the cache, but internet access has been disabled.
    /// * The package uses a legacy format not supported anymore.
    ///
    /// The intended use is to track them in an enum and assign them to this type. You can also
    /// assign [`String`] as placeholder.
    type M: Eq + Clone + Debug + Display;

    /// [Decision making](https://github.com/dart-lang/pub/blob/master/doc/solver.md#decision-making)
    /// is the process of choosing the next package
    /// and version that will be appended to the partial solution.
    ///
    /// Every time such a decision must be made, the resolver looks at all the potential valid
    /// packages that have changed, and a asks the dependency provider how important each one is.
    /// For each one it calls `prioritize` with the name of the package and the current set of
    /// acceptable versions.
    /// The resolver will then pick the package with the highes priority from all the potential valid
    /// packages.
    ///
    /// The strategy employed to prioritize packages
    /// cannot change the existence of a solution or not,
    /// but can drastically change the performances of the solver,
    /// or the properties of the solution.
    /// The documentation of Pub (PubGrub implementation for the dart programming language)
    /// states the following:
    ///
    /// > Pub chooses the latest matching version of the package
    /// > with the fewest versions that match the outstanding constraint.
    /// > This tends to find conflicts earlier if any exist,
    /// > since these packages will run out of versions to try more quickly.
    /// > But there's likely room for improvement in these heuristics.
    ///
    /// Note: the resolver may call this even when the range has not change,
    /// if it is more efficient for the resolveres internal data structures.
    fn prioritize(&self, package: &Self::P, range: &Self::VS) -> Self::Priority;
    /// The type returned from `prioritize`. The resolver does not care what type this is
    /// as long as it can pick a largest one and clone it.
    ///
    /// [std::cmp::Reverse] can be useful if you want to pick the package with
    /// the fewest versions that match the outstanding constraint.
    type Priority: Ord + Clone;

    /// The kind of error returned from these methods.
    ///
    /// Returning this signals that resolution should fail with this error.
    type Err: Error + 'static;

    /// Once the resolver has found the highest `Priority` package from all potential valid
    /// packages, it needs to know what vertion of that package to use. The most common pattern
    /// is to select the largest vertion that the range contains.
    fn choose_version(
        &self,
        package: &Self::P,
        range: &Self::VS,
    ) -> Result<Option<Self::V>, Self::Err>;

    /// Retrieves the package dependencies.
    /// Return [Dependencies::Unavailable] if its dependencies are unavailable.

    fn get_dependencies<DV: DependencyVisitor<Self::P, Self::VS, Self::M>>(
        &self,
        package: &Self::P,
        version: &Self::V,
        dependency_adder: &mut DV,
    ) -> Result<(), Self::Err>;

    /// This is called fairly regularly during the resolution,
    /// if it returns an Err then resolution will be terminated.
    /// This is helpful if you want to add some form of early termination like a timeout,
    /// or you want to add some form of user feedback if things are taking a while.
    /// If not provided the resolver will run as long as needed.
    fn should_cancel(&self) -> Result<(), Self::Err> {
        Ok(())
    }
}

/// A basic implementation of [DependencyProvider].
#[derive(Debug, Clone, Default)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[cfg_attr(
    feature = "serde",
    serde(bound(
        serialize = "VS::V: serde::Serialize, VS: serde::Serialize, P: serde::Serialize",
        deserialize = "VS::V: serde::Deserialize<'de>, VS: serde::Deserialize<'de>, P: serde::Deserialize<'de>"
    ))
)]
#[cfg_attr(feature = "serde", serde(transparent))]
pub struct OfflineDependencyProvider<P: Package, VS: VersionSet> {
    dependencies: Map<P, BTreeMap<VS::V, Map<P, VS>>>,
}

impl<P: Package, VS: VersionSet> OfflineDependencyProvider<P, VS> {
    /// Creates an empty OfflineDependencyProvider with no dependencies.
    pub fn new() -> Self {
        Self {
            dependencies: Map::default(),
        }
    }

    /// Registers the dependencies of a package and version pair.
    /// Dependencies must be added with a single call to
    /// [add_dependencies](OfflineDependencyProvider::add_dependencies).
    /// All subsequent calls to
    /// [add_dependencies](OfflineDependencyProvider::add_dependencies) for a given
    /// package version pair will replace the dependencies by the new ones.
    ///
    /// The API does not allow to add dependencies one at a time to uphold an assumption that
    /// [OfflineDependencyProvider.get_dependencies(p, v)](OfflineDependencyProvider::get_dependencies)
    /// provides all dependencies of a given package (p) and version (v) pair.
    pub fn add_dependencies<I: IntoIterator<Item = (P, VS)>>(
        &mut self,
        package: P,
        version: impl Into<VS::V>,
        dependencies: I,
    ) {
        let package_deps = dependencies.into_iter().collect();
        let v = version.into();
        *self
            .dependencies
            .entry(package)
            .or_default()
            .entry(v)
            .or_default() = package_deps;
    }

    /// Lists packages that have been saved.
    pub fn packages(&self) -> impl Iterator<Item = &P> {
        self.dependencies.keys()
    }

    /// Lists versions of saved packages in sorted order.
    /// Returns [None] if no information is available regarding that package.
    pub fn versions(&self, package: &P) -> Option<impl Iterator<Item = &VS::V>> {
        self.dependencies.get(package).map(|k| k.keys())
    }

    /// Lists dependencies of a given package and version.
    /// Returns [None] if no information is available regarding that package and version pair.
    fn dependencies(&self, package: &P, version: &VS::V) -> Option<&Map<P, VS>> {
        self.dependencies.get(package)?.get(version)
    }
}

/// An implementation of [DependencyProvider] that
/// contains all dependency information available in memory.
/// Currently packages are picked with the fewest versions contained in the constraints first.
/// But, that may change in new versions if better heuristics are found.
/// Versions are picked with the newest versions first.
impl<P: Package, VS: VersionSet> DependencyProvider for OfflineDependencyProvider<P, VS> {
    type P = P;
    type V = VS::V;
    type VS = VS;
    type M = String;

    type Err = Infallible;

    fn choose_version(&self, package: &P, range: &VS) -> Result<Option<VS::V>, Infallible> {
        Ok(self
            .dependencies
            .get(package)
            .and_then(|versions| versions.keys().rev().find(|v| range.contains(v)).cloned()))
    }

    type Priority = Reverse<usize>;
    fn prioritize(&self, package: &P, range: &VS) -> Self::Priority {
        Reverse(
            self.dependencies
                .get(package)
                .map(|versions| versions.keys().filter(|v| range.contains(v)).count())
                .unwrap_or(0),
        )
    }

    fn get_dependencies<DV: DependencyVisitor<Self::P, Self::VS, Self::M>>(
        &self,
        package: &P,
        version: &VS::V,
        dependency_adder: &mut DV,
    ) -> Result<(), Infallible> {
        match self.dependencies(package, version) {
            None => dependency_adder
                .make_unavailable_reason("its dependencies could not be determined".to_string()),
            Some(dependencies) => dependency_adder
                .add_iter_dependencies(dependencies.iter().map(|(d, vs)| (d.clone(), vs.clone()))),
        };
        Ok(())
    }
}
