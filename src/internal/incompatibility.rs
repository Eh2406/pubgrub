// SPDX-License-Identifier: MPL-2.0

//! An incompatibility is a set of terms for different packages
//! that should never be satisfied all together.

use std::fmt::{Debug, Display};
use std::sync::Arc;

use crate::internal::{small_map, Arena, HashArena, Id, SmallMap};
use crate::{
    term, DependencyProvider, DerivationTree, Derived, External, Map, Package, Set, Term,
    VersionSet,
};

/// An incompatibility is a set of terms for different packages
/// that should never be satisfied all together.
/// An incompatibility usually originates from a package dependency.
/// For example, if package A at version 1 depends on package B
/// at version 2, you can never have both terms `A = 1`
/// and `not B = 2` satisfied at the same time in a partial solution.
/// This would mean that we found a solution with package A at version 1
/// but not with package B at version 2.
/// Yet A at version 1 depends on B at version 2 so this is not possible.
/// Therefore, the set `{ A = 1, not B = 2 }` is an incompatibility,
/// defined from dependencies of A at version 1.
///
/// Incompatibilities can also be derived from two other incompatibilities
/// during conflict resolution. More about all this in
/// [PubGrub documentation](https://github.com/dart-lang/pub/blob/master/doc/solver.md#incompatibility).
#[derive(Debug, Clone)]
pub(crate) struct Incompatibility<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    kind: Kind<P, VS, M>,
}

/// Type alias of unique identifiers for incompatibilities.
pub(crate) type IncompId<P, VS, M> = Id<Incompatibility<P, VS, M>>;

pub(crate) type IncompDpId<DP> = IncompId<
    <DP as DependencyProvider>::P,
    <DP as DependencyProvider>::VS,
    <DP as DependencyProvider>::M,
>;

#[derive(Debug, Clone)]
enum Kind<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> {
    /// Initial incompatibility aiming at picking the root package for the first decision.
    ///
    /// This incompatibility drives the resolution, it requires that we pick the (virtual) root
    /// packages.
    NotRoot(Id<P>, Term<VS>, VS::V),
    /// There are no versions in the given range for this package.
    ///
    /// This incompatibility is used when we tried all versions in a range and no version
    /// worked, so we have to backtrack
    NoVersions(Id<P>, Term<VS>),
    /// Incompatibility coming from the dependencies of a given package.
    ///
    /// If a@1 depends on b>=1,<2, we create an incompatibility with terms `{a 1, b <1,>=2}` with
    /// kind `FromDependencyOf(a, 1, b, >=1,<2)`.
    ///
    /// We can merge multiple dependents with the same version. For example, if a@1 depends on b and
    /// a@2 depends on b, we can say instead a@1||2 depends on b.
    FromDependencyOf(Id<P>, Term<VS>, Id<P>, Option<Term<VS>>),
    /// Derived from two causes. Stores cause ids.
    ///
    /// For example, if a -> b and b -> c, we can derive a -> c.
    DerivedFrom(
        IncompId<P, VS, M>,
        IncompId<P, VS, M>,
        SmallMap<Id<P>, Term<VS>>,
    ),
    /// The package is unavailable for reasons outside pubgrub.
    ///
    /// Examples:
    /// * The version would require building the package, but builds are disabled.
    /// * The package is not available in the cache, but internet access has been disabled.
    Custom(Id<P>, Term<VS>, M),
}

/// A Relation describes how a set of terms can be compared to an incompatibility.
/// Typically, the set of terms comes from the partial solution.
#[derive(Eq, PartialEq, Debug)]
pub(crate) enum Relation<P: Package> {
    /// We say that a set of terms S satisfies an incompatibility I
    /// if S satisfies every term in I.
    Satisfied,
    /// We say that S contradicts I
    /// if S contradicts at least one term in I.
    Contradicted(Id<P>),
    /// If S satisfies all but one of I's terms and is inconclusive for the remaining term,
    /// we say S "almost satisfies" I and we call the remaining term the "unsatisfied term".
    AlmostSatisfied(Id<P>),
    /// Otherwise, we say that their relation is inconclusive.
    Inconclusive,
}

#[allow(clippy::type_complexity)]
pub(crate) enum IncompatibilityIter<'a, P, VS: VersionSet> {
    One(std::array::IntoIter<(Id<P>, &'a Term<VS>), 1>),
    Two(std::array::IntoIter<(Id<P>, &'a Term<VS>), 2>),
    Many(
        std::iter::Map<
            small_map::IterSmallMap<'a, Id<P>, Term<VS>>,
            fn((&'a Id<P>, &'a Term<VS>)) -> (Id<P>, &'a Term<VS>),
        >,
    ),
}

impl<'a, P, VS: VersionSet> Iterator for IncompatibilityIter<'a, P, VS> {
    type Item = (Id<P>, &'a Term<VS>);

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            IncompatibilityIter::One(i) => i.next(),
            IncompatibilityIter::Two(i) => i.next(),
            IncompatibilityIter::Many(i) => i.next(),
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        match self {
            IncompatibilityIter::One(i) => i.size_hint(),
            IncompatibilityIter::Two(i) => i.size_hint(),
            IncompatibilityIter::Many(i) => i.size_hint(),
        }
    }
}

impl<P, VS: VersionSet> ExactSizeIterator for IncompatibilityIter<'_, P, VS> {}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Incompatibility<P, VS, M> {
    /// Create the initial "not Root" incompatibility.
    pub(crate) fn not_root(package: Id<P>, version: VS::V) -> Self {
        Self {
            kind: Kind::NotRoot(
                package,
                Term::Negative(VS::singleton(version.clone())),
                version,
            ),
        }
    }

    /// Create an incompatibility to remember that a given set does not contain any version.
    pub(crate) fn no_versions(package: Id<P>, term: Term<VS>) -> Self {
        if let Term::Negative(_) = &term {
            panic!("No version should have a positive term")
        };
        Self {
            kind: Kind::NoVersions(package, term),
        }
    }

    /// Create an incompatibility for a reason outside pubgrub.
    #[allow(dead_code)] // Used by uv
    pub(crate) fn custom_term(package: Id<P>, term: Term<VS>, metadata: M) -> Self {
        if let Term::Negative(_) = &term {
            panic!("No version should have a positive term")
        };
        Self {
            kind: Kind::Custom(package, term, metadata),
        }
    }

    /// Create an incompatibility for a reason outside pubgrub.
    pub(crate) fn custom_version(package: Id<P>, version: VS::V, metadata: M) -> Self {
        let set = VS::singleton(version);
        let term = Term::Positive(set.clone());
        Self {
            kind: Kind::Custom(package, term, metadata),
        }
    }

    /// Build an incompatibility from a given dependency.
    pub(crate) fn from_dependency(package: Id<P>, versions: VS, dep: (Id<P>, VS)) -> Self {
        let (p2, set2) = dep;
        Self {
            kind: Kind::FromDependencyOf(
                package,
                Term::Positive(versions.clone()),
                p2,
                (set2 != VS::empty()).then_some(Term::Negative(set2.clone())),
            ),
        }
    }

    pub(crate) fn as_dependency(&self) -> Option<(Id<P>, Id<P>)> {
        match &self.kind {
            Kind::FromDependencyOf(p1, _, p2, _) => Some((*p1, *p2)),
            _ => None,
        }
    }

    /// Merge dependant versions with the same dependency.
    ///
    /// When multiple versions of a package depend on the same range of another package,
    /// we can merge the two into a single incompatibility.
    /// For example, if a@1 depends on b and a@2 depends on b, we can say instead
    /// a@1||2 depends on b.
    ///
    /// It is a special case of prior cause computation where the unified package
    /// is the common dependant in the two incompatibilities expressing dependencies.
    pub(crate) fn merge_dependents(&self, other: &Self) -> Option<Self> {
        // It is almost certainly a bug to call this method without checking that self is a dependency
        debug_assert!(self.as_dependency().is_some());
        // Check that both incompatibilities are of the shape p1 depends on p2,
        // with the same p1 and p2.
        let self_pkgs = self.as_dependency()?;
        if self_pkgs != other.as_dependency()? {
            return None;
        }
        let (p1, p2) = self_pkgs;
        let dep_term = self.get(p2);
        // The dependency range for p2 must be the same in both case
        // to be able to merge multiple p1 ranges.
        if dep_term != other.get(p2) {
            return None;
        }
        Some(Self::from_dependency(
            p1,
            self.get(p1)
                .unwrap()
                .unwrap_positive()
                .union(other.get(p1).unwrap().unwrap_positive()), // It is safe to `simplify` here
            (
                p2,
                dep_term.map_or(VS::empty(), |v| v.unwrap_negative().clone()),
            ),
        ))
    }

    /// Prior cause of two incompatibilities using the rule of resolution.
    pub(crate) fn prior_cause(
        incompat: Id<Self>,
        satisfier_cause: Id<Self>,
        package: Id<P>,
        incompatibility_store: &Arena<Self>,
    ) -> Self {
        // Optimization to avoid cloning and dropping t1
        let package_terms = incompatibility_store[incompat].clone_into_small_map();
        let (t1, mut package_terms) = package_terms.split_one(&package).unwrap();
        let satisfier_cause_terms = &incompatibility_store[satisfier_cause];
        package_terms.merge(
            satisfier_cause_terms.iter().filter(|(p, _)| p != &package),
            |t1, t2| Some(t1.intersection(t2)),
        );
        let term = t1.union(satisfier_cause_terms.get(package).unwrap());
        if term != Term::any() {
            package_terms.insert(package, term);
        }
        Self {
            kind: Kind::DerivedFrom(incompat, satisfier_cause, package_terms),
        }
    }

    /// Check if an incompatibility should mark the end of the algorithm
    /// because it satisfies the root package.
    pub(crate) fn is_terminal(&self, root_package: Id<P>, root_version: &VS::V) -> bool {
        let mut iter = self.iter();
        let Some((package, term)) = iter.next() else {
            return true;
        };
        if iter.next().is_some() {
            return false;
        }
        if package != root_package {
            return false;
        }
        term.contains(root_version)
    }

    /// Get the term related to a given package (if it exists).
    pub(crate) fn get(&self, package: Id<P>) -> Option<&Term<VS>> {
        match &self.kind {
            Kind::NotRoot(id, vs, _) | Kind::NoVersions(id, vs) | Kind::Custom(id, vs, _) => {
                (id == &package).then_some(vs)
            }
            Kind::FromDependencyOf(id, vs, id1, t1) => (id == &package)
                .then_some(vs)
                .or_else(|| if id1 == &package { t1.as_ref() } else { None }),
            Kind::DerivedFrom(_, _, small_map) => small_map.get(&package),
        }
    }

    fn clone_into_small_map(&self) -> SmallMap<Id<P>, Term<VS>> {
        match &self.kind {
            Kind::NotRoot(id, vs, _) | Kind::NoVersions(id, vs) | Kind::Custom(id, vs, _) => {
                let mut map = SmallMap::Empty;
                map.insert(*id, vs.clone());
                map
            }
            Kind::FromDependencyOf(id, vs, id1, t1) => {
                let mut map = SmallMap::Empty;
                map.insert(*id, vs.clone());
                if let Some(t1) = t1 {
                    map.insert(*id1, t1.clone());
                }
                map
            }
            Kind::DerivedFrom(_, _, small_map) => small_map.clone(),
        }
    }

    /// Iterate over packages.
    pub(crate) fn iter(&self) -> IncompatibilityIter<P, VS> {
        fn deref_first<P, V>((id, v): (&Id<P>, V)) -> (Id<P>, V) {
            (*id, v)
        }
        match &self.kind {
            Kind::NotRoot(id, vs, _)
            | Kind::NoVersions(id, vs)
            | Kind::Custom(id, vs, _)
            | Kind::FromDependencyOf(id, vs, _, None) => {
                IncompatibilityIter::One([(*id, vs)].into_iter())
            }
            Kind::FromDependencyOf(id, vs, id1, Some(t1)) => {
                IncompatibilityIter::Two([(*id, vs), (*id1, t1)].into_iter())
            }
            Kind::DerivedFrom(_, _, package_terms) => {
                IncompatibilityIter::Many(package_terms.iter().map(deref_first::<P, &Term<VS>>))
            }
        }
    }

    // Reporting ###############################################################

    /// Retrieve parent causes if of type DerivedFrom.
    pub(crate) fn causes(&self) -> Option<(Id<Self>, Id<Self>)> {
        match self.kind {
            Kind::DerivedFrom(id1, id2, _) => Some((id1, id2)),
            _ => None,
        }
    }

    /// Build a derivation tree for error reporting.
    pub(crate) fn build_derivation_tree(
        self_id: Id<Self>,
        shared_ids: &Set<Id<Self>>,
        store: &Arena<Self>,
        package_store: &HashArena<P>,
        precomputed: &Map<Id<Self>, Arc<DerivationTree<P, VS, M>>>,
    ) -> DerivationTree<P, VS, M> {
        match store[self_id].kind.clone() {
            Kind::DerivedFrom(id1, id2, _) => {
                let derived: Derived<P, VS, M> = Derived {
                    terms: store[self_id]
                        .iter()
                        .map(|(a, b)| (package_store[a].clone(), b.clone()))
                        .collect(),
                    shared_id: shared_ids.get(&self_id).map(|id| id.into_raw()),
                    cause1: precomputed
                        .get(&id1)
                        .expect("Non-topological calls building tree")
                        .clone(),
                    cause2: precomputed
                        .get(&id2)
                        .expect("Non-topological calls building tree")
                        .clone(),
                };
                DerivationTree::Derived(derived)
            }
            Kind::NotRoot(package, _, version) => {
                DerivationTree::External(External::NotRoot(package_store[package].clone(), version))
            }
            Kind::NoVersions(package, set) => DerivationTree::External(External::NoVersions(
                package_store[package].clone(),
                set.unwrap_positive().clone(),
            )),
            Kind::FromDependencyOf(package, set, dep_package, dep_set) => {
                DerivationTree::External(External::FromDependencyOf(
                    package_store[package].clone(),
                    set.unwrap_positive().clone(),
                    package_store[dep_package].clone(),
                    dep_set
                        .unwrap_or_else(|| Term::Negative(VS::empty()))
                        .unwrap_negative()
                        .clone(),
                ))
            }
            Kind::Custom(package, set, metadata) => DerivationTree::External(External::Custom(
                package_store[package].clone(),
                set.unwrap_positive().clone(),
                metadata.clone(),
            )),
        }
    }
}

impl<'a, P: Package, VS: VersionSet + 'a, M: Eq + Clone + Debug + Display + 'a>
    Incompatibility<P, VS, M>
{
    /// CF definition of Relation enum.
    pub(crate) fn relation(&self, terms: impl Fn(Id<P>) -> Option<&'a Term<VS>>) -> Relation<P> {
        let mut relation = Relation::Satisfied;
        for (package, incompat_term) in self.iter() {
            match terms(package).map(|term| incompat_term.relation_with(term)) {
                Some(term::Relation::Satisfied) => {}
                Some(term::Relation::Contradicted) => {
                    return Relation::Contradicted(package);
                }
                None | Some(term::Relation::Inconclusive) => {
                    // If a package is not present, the intersection is the same as [Term::any].
                    // According to the rules of satisfactions, the relation would be inconclusive.
                    // It could also be satisfied if the incompatibility term was also [Term::any],
                    // but we systematically remove those from incompatibilities
                    // so we're safe on that front.
                    if relation == Relation::Satisfied {
                        relation = Relation::AlmostSatisfied(package);
                    } else {
                        return Relation::Inconclusive;
                    }
                }
            }
        }
        relation
    }
}

impl<P: Package, VS: VersionSet, M: Eq + Clone + Debug + Display> Incompatibility<P, VS, M> {
    pub fn display<'a>(&'a self, package_store: &'a HashArena<P>) -> impl Display + 'a {
        match self.iter().collect::<Vec<_>>().as_slice() {
            [] => "version solving failed".into(),
            // TODO: special case when that unique package is root.
            [(package, Term::Positive(range))] => {
                format!("{} {} is forbidden", package_store[*package], range)
            }
            [(package, Term::Negative(range))] => {
                format!("{} {} is mandatory", package_store[*package], range)
            }
            [(p_pos, Term::Positive(r_pos)), (p_neg, Term::Negative(r_neg))]
            | [(p_neg, Term::Negative(r_neg)), (p_pos, Term::Positive(r_pos))] => {
                External::<_, _, M>::FromDependencyOf(
                    &package_store[*p_pos],
                    r_pos.clone(),
                    &package_store[*p_neg],
                    r_neg.clone(),
                )
                .to_string()
            }
            slice => {
                let str_terms: Vec<_> = slice
                    .iter()
                    .map(|(p, t)| format!("{} {}", package_store[*p], t))
                    .collect();
                str_terms.join(", ") + " are incompatible"
            }
        }
    }
}
