use std::{borrow::Cow, collections::BTreeSet, hash::BuildHasherDefault};

use indexmap::IndexMap;
use rustc_hash::FxHasher;
use thiserror::Error;

use crate::v0::table::{NodeId, RegionId};

type FxIndexMap<K, V> = IndexMap<K, V, BuildHasherDefault<FxHasher>>;

/// Borrowed symbol name used as a lookup key in scoped symbol tables.
pub type SymbolName<'a> = &'a str;

/// Symbol binding table that keeps track of symbol resolution and scoping.
///
/// Nodes may introduce a symbol so that other parts of the IR can refer to the
/// node. Symbols have an associated name and are scoped via regions. A symbol
/// can shadow another symbol with the same name from an outer region, but
/// within any single region each name/version pair must be unique. Versioned
/// references resolve exactly. Unversioned references prefer an unversioned
/// binding, then the latest visible versioned binding.
///
/// When a symbol is referred to directly by the id of the node, the symbol must
/// be in scope at the point of reference as if the reference was by name. This
/// guarantees that transformations between directly indexed and named formats
/// are always valid.
///
/// # Examples
///
/// ```
/// # pub use hugr_model::v0::table::{NodeId, RegionId};
/// # pub use hugr_model::v0::scope::SymbolTable;
/// let mut symbols = SymbolTable::new();
/// symbols.enter(RegionId(0));
/// symbols.insert("foo", None, NodeId(0)).unwrap();
/// assert_eq!(symbols.resolve("foo", None).unwrap(), NodeId(0));
/// symbols.enter(RegionId(1));
/// assert_eq!(symbols.resolve("foo", None).unwrap(), NodeId(0));
/// symbols.insert("foo", None, NodeId(1)).unwrap();
/// assert_eq!(symbols.resolve("foo", None).unwrap(), NodeId(1));
/// assert!(!symbols.is_visible(NodeId(0)));
/// symbols.exit();
/// assert_eq!(symbols.resolve("foo", None).unwrap(), NodeId(0));
/// assert!(symbols.is_visible(NodeId(0)));
/// assert!(!symbols.is_visible(NodeId(1)));
/// ```
#[derive(Debug, Clone, Default)]
pub struct SymbolTable<'a> {
    symbols: FxIndexMap<SymbolKey<'a>, BindingIndex>,
    bindings: FxIndexMap<NodeId, Binding>,
    scopes: FxIndexMap<RegionId, Scope>,
    latest_versioned: FxIndexMap<SymbolName<'a>, BTreeSet<semver::Version>>,
}

impl<'a> SymbolTable<'a> {
    /// Create a new symbol table.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Enter a new scope for the given region.
    pub fn enter(&mut self, region: RegionId) {
        self.scopes.insert(
            region,
            Scope {
                binding_stack: self.bindings.len(),
            },
        );
    }

    /// Exit a previously entered scope.
    ///
    /// # Panics
    ///
    /// Panics if there are no remaining open scopes.
    pub fn exit(&mut self) {
        let (_, scope) = self.scopes.pop().unwrap();

        for _ in scope.binding_stack..self.bindings.len() {
            let (_, binding) = self.bindings.pop().unwrap();
            let key = self
                .symbols
                .get_index(binding.symbol_index)
                .expect("Symbol must be present in version table")
                .0
                .clone();

            if let Some(shadows) = binding.shadows {
                self.symbols[binding.symbol_index] = shadows;
            } else {
                let last = self.symbols.pop();
                debug_assert_eq!(last.unwrap().1, self.bindings.len());
                self.remove_latest_versioned(&key);
            }
        }
    }

    /// Insert a new symbol into the current scope.
    ///
    /// # Errors
    ///
    /// Returns an error if the symbol is already defined in the current scope.
    /// In the case of an error the table remains unchanged.
    ///
    /// # Panics
    ///
    /// Panics if there is no current scope.
    pub fn insert(
        &mut self,
        name: SymbolName<'a>,
        version: Option<&semver::Version>,
        node: NodeId,
    ) -> Result<(), DuplicateSymbolError<'_>> {
        self.insert_binding(name, version, node)
    }

    /// Insert a new import into the current scope.
    ///
    /// # Errors
    ///
    /// Returns an error if the import is already defined in the current scope.
    /// In the case of an error the table remains unchanged.
    ///
    /// # Panics
    ///
    /// Panics if there is no current scope.
    pub fn insert_import(
        &mut self,
        name: SymbolName<'a>,
        version: Option<&semver::Version>,
        node: NodeId,
    ) -> Result<(), DuplicateSymbolError<'_>> {
        self.insert_binding(name, version, node)
    }

    fn insert_binding(
        &mut self,
        name: SymbolName<'a>,
        version: Option<&semver::Version>,
        node: NodeId,
    ) -> Result<(), DuplicateSymbolError<'_>> {
        let key = SymbolKey::new(name, version);
        let scope_depth = self.scopes.len() as u16 - 1;
        let (symbol_index, shadowed) = self.symbols.insert_full(key.clone(), self.bindings.len());

        if let Some(shadowed) = shadowed {
            let (shadowed_node, shadowed_binding) = self.bindings.get_index(shadowed).unwrap();
            if shadowed_binding.scope_depth == scope_depth {
                self.symbols.insert(key, shadowed);
                return Err(DuplicateSymbolError(name.into(), node, *shadowed_node));
            }
        }

        self.insert_latest_versioned(&key);

        self.bindings.insert(
            node,
            Binding {
                scope_depth,
                shadows: shadowed,
                symbol_index,
            },
        );

        Ok(())
    }

    /// Check whether a symbol is currently visible in the current scope.
    #[must_use]
    pub fn is_visible(&self, node: NodeId) -> bool {
        let Some(binding) = self.bindings.get(&node) else {
            return false;
        };

        // Check that the symbol has not been shadowed at this point.
        self.symbols[binding.symbol_index] == binding.symbol_index
    }

    /// Tries to resolve a symbol name in the current scope.
    pub fn resolve(
        &self,
        name: SymbolName<'a>,
        version: Option<&semver::Version>,
    ) -> Result<NodeId, UnknownSymbolError<'_>> {
        let index = match version {
            Some(version) => self
                .symbols
                .get(&SymbolKey::new(name, Some(version)))
                .copied(),
            None => self
                .symbols
                .get(&SymbolKey::new(name, None))
                .copied()
                .or_else(|| self.latest_versioned(name)),
        }
        .ok_or(UnknownSymbolError(name.into()))?;

        // NOTE: The unwrap is safe because the `symbols` map
        // points to valid indices in the `bindings` map.
        let (node, _) = self.bindings.get_index(index).unwrap();
        Ok(*node)
    }

    /// Return the latest visible versioned binding for `name`.
    ///
    /// The primary symbol map is kept in insertion order so scopes can be
    /// unwound as a stack. This side index groups the currently visible
    /// versioned bindings by symbol name to speed up the lookup of the latest
    /// declared version.
    fn latest_versioned(&self, name: SymbolName<'a>) -> Option<BindingIndex> {
        let latest = self.latest_versioned.get(name)?.last()?;
        self.symbols
            .get(&SymbolKey::new(name, Some(latest)))
            .copied()
    }

    /// Add `key` to the latest-version side index if it is versioned.
    fn insert_latest_versioned(&mut self, key: &SymbolKey<'a>) {
        let Some(version) = &key.version else {
            return;
        };

        self.latest_versioned
            .entry(key.name)
            .or_default()
            .insert(version.clone());
    }

    /// Remove a versioned binding from the side index.
    fn remove_latest_versioned(&mut self, key: &SymbolKey<'a>) {
        let Some(version) = &key.version else {
            return;
        };

        let Some(versions) = self.latest_versioned.get_mut(key.name) else {
            return;
        };

        versions.remove(version);
        if versions.is_empty() {
            self.latest_versioned.swap_remove(key.name);
        }
    }

    /// Returns the depth of the given region, if it corresponds to a currently open scope.
    #[must_use]
    pub fn region_to_depth(&self, region: RegionId) -> Option<ScopeDepth> {
        Some(self.scopes.get_index_of(&region)? as _)
    }

    /// Returns the region corresponding to the scope at the given depth.
    #[must_use]
    pub fn depth_to_region(&self, depth: ScopeDepth) -> Option<RegionId> {
        let (region, _) = self.scopes.get_index(depth as _)?;
        Some(*region)
    }

    /// Resets the symbol table to its initial state while maintaining its
    /// allocated memory.
    pub fn clear(&mut self) {
        self.symbols.clear();
        self.bindings.clear();
        self.scopes.clear();
        self.latest_versioned.clear();
    }
}

/// Symbol lookup key for a name and optional extension version.
///
/// The version is optional so the table can represent both legacy unversioned
/// symbols and modern versioned extension symbols. `None` is a real binding key,
/// not a wildcard; wildcard/default behavior is handled explicitly by
/// [`SymbolTable::resolve`].
///
/// TODO: Remove the legacy unversioned path once encoded HUGRs without
/// extension version information are no longer supported.
/// <http://github.com/Quantinuum/hugr/issues/???>
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct SymbolKey<'a> {
    name: SymbolName<'a>,
    version: Option<semver::Version>,
}

impl<'a> SymbolKey<'a> {
    fn new(name: SymbolName<'a>, version: Option<&semver::Version>) -> Self {
        Self {
            name,
            version: version.cloned(),
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Binding {
    /// The depth of the scope in which this binding is defined.
    scope_depth: ScopeDepth,

    /// The index of the binding that is shadowed by this one, if any.
    shadows: Option<BindingIndex>,

    /// The index of this binding's symbol in the symbol table.
    ///
    /// The symbol table always points to the currently visible binding for a
    /// symbol. Therefore this index is only valid if this binding is not shadowed.
    /// In particular, we detect shadowing by checking if the entry in the symbol
    /// table at this index does indeed point to this binding.
    symbol_index: SymbolIndex,
}

#[derive(Debug, Clone, Copy)]
struct Scope {
    /// The length of the `bindings` stack when this scope was entered.
    binding_stack: usize,
}

type BindingIndex = usize;
type SymbolIndex = usize;

pub type ScopeDepth = u16;

/// Error that occurs when trying to resolve an unknown symbol.
#[derive(Debug, Clone, Error)]
#[error("symbol name `{0}` not found in this scope")]
pub struct UnknownSymbolError<'a>(pub Cow<'a, str>);

/// Error that occurs when trying to introduce a symbol that is already defined in the current scope.
#[derive(Debug, Clone, Error)]
#[error("symbol `{0}` is already defined in this scope")]
pub struct DuplicateSymbolError<'a>(pub Cow<'a, str>, pub NodeId, pub NodeId);

#[cfg(test)]
mod tests {
    use super::*;
    use rstest::{fixture, rstest};

    #[derive(Debug, Clone, Copy)]
    enum BindingSource {
        Import,
        Symbol,
    }

    impl BindingSource {
        fn insert(
            self,
            symbols: &mut SymbolTable<'static>,
            name: &'static str,
            version: Option<&semver::Version>,
            node: NodeId,
        ) {
            match self {
                Self::Import => symbols.insert_import(name, version, node).unwrap(),
                Self::Symbol => symbols.insert(name, version, node).unwrap(),
            }
        }
    }

    #[fixture]
    fn symbols() -> SymbolTable<'static> {
        let mut symbols = SymbolTable::new();
        symbols.enter(RegionId(0));
        symbols
    }

    fn version(version: &str) -> semver::Version {
        version.parse().unwrap()
    }

    /// Unversioned references resolve to the latest visible versioned binding.
    #[rstest]
    #[case::imports(BindingSource::Import)]
    #[case::symbols(BindingSource::Symbol)]
    fn latest_version(
        #[case] source: BindingSource,
        #[from(symbols)] mut symbols: SymbolTable<'static>,
    ) {
        let older = version("1.2.3");
        let newer = version("1.3.0");

        source.insert(&mut symbols, "std.int.add", Some(&older), NodeId(0));
        source.insert(&mut symbols, "std.int.add", Some(&newer), NodeId(1));

        assert_eq!(symbols.resolve("std.int.add", None).unwrap(), NodeId(1));
        assert_eq!(
            symbols.resolve("std.int.add", Some(&older)).unwrap(),
            NodeId(0)
        );
        assert_eq!(
            symbols.resolve("std.int.add", Some(&newer)).unwrap(),
            NodeId(1)
        );
    }

    /// A single visible versioned binding can be inferred from an unversioned use.
    #[rstest]
    #[case::imports(BindingSource::Import)]
    #[case::symbols(BindingSource::Symbol)]
    fn single_version(
        #[case] source: BindingSource,
        #[from(symbols)] mut symbols: SymbolTable<'static>,
    ) {
        let version = version("1.2.3");
        source.insert(&mut symbols, "std.int.add", Some(&version), NodeId(0));

        assert_eq!(symbols.resolve("std.int.add", None).unwrap(), NodeId(0));
    }

    /// An exact unversioned binding is separate from versioned extension bindings.
    #[rstest]
    fn unversioned_is_exact(#[from(symbols)] mut symbols: SymbolTable<'static>) {
        let version = version("1.2.3");

        symbols.insert("std.int.add", None, NodeId(0)).unwrap();
        symbols
            .insert_import("std.int.add", Some(&version), NodeId(1))
            .unwrap();

        assert_eq!(symbols.resolve("std.int.add", None).unwrap(), NodeId(0));
        assert_eq!(
            symbols.resolve("std.int.add", Some(&version)).unwrap(),
            NodeId(1)
        );
    }

    /// Leaving a scope restores the latest visible version from the outer scope.
    #[rstest]
    #[case::imports(BindingSource::Import)]
    #[case::symbols(BindingSource::Symbol)]
    fn latest_after_exit(
        #[case] source: BindingSource,
        #[from(symbols)] mut symbols: SymbolTable<'static>,
    ) {
        let older = version("1.2.3");
        let newer = version("1.3.0");

        source.insert(&mut symbols, "std.int.add", Some(&older), NodeId(0));
        symbols.enter(RegionId(1));
        source.insert(&mut symbols, "std.int.add", Some(&newer), NodeId(1));

        assert_eq!(symbols.resolve("std.int.add", None).unwrap(), NodeId(1));

        symbols.exit();

        assert_eq!(symbols.resolve("std.int.add", None).unwrap(), NodeId(0));
    }

    /// Shadowing the same version restores the shadowed binding on scope exit.
    #[rstest]
    #[case::imports(BindingSource::Import)]
    #[case::symbols(BindingSource::Symbol)]
    fn latest_shadowed(
        #[case] source: BindingSource,
        #[from(symbols)] mut symbols: SymbolTable<'static>,
    ) {
        let version = version("1.2.3");

        source.insert(&mut symbols, "std.int.add", Some(&version), NodeId(0));
        symbols.enter(RegionId(1));
        source.insert(&mut symbols, "std.int.add", Some(&version), NodeId(1));

        assert_eq!(symbols.resolve("std.int.add", None).unwrap(), NodeId(1));

        symbols.exit();

        assert_eq!(symbols.resolve("std.int.add", None).unwrap(), NodeId(0));
    }
}
