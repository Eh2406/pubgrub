// SPDX-License-Identifier: MPL-2.0

use std::cell::RefCell;
use std::collections::BTreeMap;

use pubgrub::range::Range;
use pubgrub::solver::{
    resolve, DependencyCollector, DependencyProvider, DependencyVisitor, OfflineDependencyProvider,
};
use pubgrub::type_aliases::Map;

type NumVS = Range<u32>;

// An example implementing caching dependency provider that will
// store queried dependencies in memory and check them before querying more from remote.
struct CachingDependencyProvider<DP: DependencyProvider> {
    remote_dependencies: DP,
    #[allow(clippy::type_complexity)]
    cached_dependencies: RefCell<Map<DP::P, BTreeMap<DP::V, DependencyCollector<DP>>>>,
}

impl<DP: DependencyProvider> CachingDependencyProvider<DP> {
    pub fn new(remote_dependencies_provider: DP) -> Self {
        CachingDependencyProvider {
            remote_dependencies: remote_dependencies_provider,
            cached_dependencies: RefCell::default(),
        }
    }
}

impl<DP: DependencyProvider<M = String>> DependencyProvider for CachingDependencyProvider<DP> {
    // Caches dependencies if they were already queried
    fn get_dependencies<DV: DependencyVisitor<Self::P, Self::VS, Self::M>>(
        &self,
        package: &Self::P,
        version: &Self::V,
        dependency_adder: &mut DV,
    ) -> Result<(), Self::Err> {
        let mut cache = self.cached_dependencies.borrow_mut();
        if let Some(deps) = cache.get(package).and_then(|s| s.get(version)) {
            deps.replay(dependency_adder);
            return Ok(());
        }
        let mut dv = DependencyCollector::<DP>::new();
        self.remote_dependencies
            .get_dependencies(package, version, &mut dv)?;
        dv.replay(dependency_adder);

        cache
            .entry(package.clone())
            .or_default()
            .entry(version.clone())
            .or_insert(dv);

        Ok(())
    }

    fn choose_version(&self, package: &DP::P, range: &DP::VS) -> Result<Option<DP::V>, DP::Err> {
        self.remote_dependencies.choose_version(package, range)
    }

    type Priority = DP::Priority;

    fn prioritize(&self, package: &DP::P, range: &DP::VS) -> Self::Priority {
        self.remote_dependencies.prioritize(package, range)
    }

    type Err = DP::Err;

    type P = DP::P;
    type V = DP::V;
    type VS = DP::VS;
    type M = DP::M;
}

fn main() {
    // Simulating remote provider locally.
    let mut remote_dependencies_provider = OfflineDependencyProvider::<&str, NumVS>::new();

    // Add dependencies as needed. Here only root package is added.
    remote_dependencies_provider.add_dependencies("root", 1u32, Vec::new());

    let caching_dependencies_provider =
        CachingDependencyProvider::new(remote_dependencies_provider);

    let solution = resolve(&caching_dependencies_provider, "root", 1u32);
    println!("Solution: {:?}", solution);
}
