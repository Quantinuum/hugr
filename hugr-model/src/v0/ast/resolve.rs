use bumpalo::{Bump, collections::Vec as BumpVec};
use itertools::zip_eq;
use rustc_hash::FxHashMap;
use thiserror::Error;

use super::{
    LinkName, Module, Node, Operation, Param, Region, SeqPart, Symbol, SymbolIdent, SymbolName,
    Term, VarName,
};
use crate::v0::{RegionKind, ScopeClosure, table};
use crate::v0::{
    scope::{LinkTable, SymbolTable, VarTable},
    table::{LinkIndex, NodeId, RegionId, TermId, VarId},
};

pub struct Context<'a> {
    module: table::Module<'a>,
    bump: &'a Bump,
    vars: VarTable<'a>,
    links: LinkTable<&'a str>,
    symbols: SymbolTable<'a>,
    imports: FxHashMap<SymbolIdent, NodeId>,
    terms: FxHashMap<table::Term<'a>, TermId>,
}

impl<'a> Context<'a> {
    /// Create an empty resolver context backed by `bump`.
    ///
    /// The context records explicit symbol versions from imports and
    /// declarations. It does not fill missing versions from any external
    /// registry; unresolved legacy versions remain `None` in the table model.
    ///
    /// TODO: Remove the `None` compatibility path once encoded HUGRs without
    /// extension version information are no longer supported.
    /// <http://github.com/Quantinuum/hugr/issues/3086>
    pub fn new(bump: &'a Bump) -> Self {
        Self {
            module: table::Module::default(),
            bump,
            vars: VarTable::new(),
            links: LinkTable::new(),
            symbols: SymbolTable::new(),
            imports: FxHashMap::default(),
            terms: FxHashMap::default(),
        }
    }

    pub fn resolve_module(&mut self, module: &'a Module) -> BuildResult<()> {
        self.module.root = self.module.insert_region(table::Region::default());
        self.symbols.enter(self.module.root);
        self.links.enter(self.module.root);

        let children = self.resolve_nodes(&module.root.children)?;
        let meta = self.resolve_terms(&module.root.meta)?;

        let (links, ports) = self.links.exit();
        self.symbols.exit();
        let scope = Some(table::RegionScope { links, ports });

        // Symbols that could not be resolved within the module still need to
        // be represented by a node. This is why we add import nodes.
        let all_children = {
            let mut all_children =
                BumpVec::with_capacity_in(children.len() + self.imports.len(), self.bump);
            all_children.extend(children);
            all_children.extend(self.imports.drain().map(|(_, node)| node));
            all_children.into_bump_slice()
        };

        self.module.regions[self.module.root.index()] = table::Region {
            kind: RegionKind::Module,
            sources: &[],
            targets: &[],
            children: all_children,
            meta,
            signature: None,
            scope,
        };

        Ok(())
    }

    fn resolve_terms(&mut self, terms: &'a [Term]) -> BuildResult<&'a [TermId]> {
        try_alloc_slice(self.bump, terms.iter().map(|term| self.resolve_term(term)))
    }

    fn resolve_term(&mut self, term: &'a Term) -> BuildResult<TermId> {
        let term = match term {
            Term::Wildcard => table::Term::Wildcard,
            Term::Var(var_name) => table::Term::Var(self.resolve_var(var_name)?),
            Term::Apply(symbol_ident, terms) => {
                let symbol_id = self.resolve_symbol_ident(symbol_ident);
                let terms = self.resolve_terms(terms)?;
                table::Term::Apply(symbol_id, terms)
            }
            Term::List(parts) => table::Term::List(self.resolve_seq_parts(parts)?),
            Term::Literal(literal) => table::Term::Literal(literal.clone()),
            Term::Tuple(parts) => table::Term::Tuple(self.resolve_seq_parts(parts)?),
            Term::Func(region) => {
                let region = self.resolve_region(region, ScopeClosure::Closed)?;
                table::Term::Func(region)
            }
        };

        Ok(*self
            .terms
            .entry(term.clone())
            .or_insert_with(|| self.module.insert_term(term)))
    }

    fn resolve_seq_parts(&mut self, parts: &'a [SeqPart]) -> BuildResult<&'a [table::SeqPart]> {
        try_alloc_slice(
            self.bump,
            parts.iter().map(|part| self.resolve_seq_part(part)),
        )
    }

    fn resolve_seq_part(&mut self, part: &'a SeqPart) -> BuildResult<table::SeqPart> {
        Ok(match part {
            SeqPart::Item(term) => table::SeqPart::Item(self.resolve_term(term)?),
            SeqPart::Splice(term) => table::SeqPart::Splice(self.resolve_term(term)?),
        })
    }

    fn resolve_nodes(&mut self, nodes: &'a [Node]) -> BuildResult<&'a [NodeId]> {
        // Allocate ids for all nodes by introducing placeholders into the module.
        let ids: &[_] = self.bump.alloc_slice_fill_with(nodes.len(), |_| {
            self.module.insert_node(table::Node::default())
        });

        // For those nodes that introduce symbols, we then associate the symbol
        // with the id of the node. This serves as a form of forward declaration
        // so that the symbol is visible in the current region regardless of the
        // order of the nodes.
        for (id, node) in zip_eq(ids, nodes) {
            if let Some((symbol_name, version)) = node.operation.symbol_binding() {
                match &node.operation {
                    Operation::Import(_) => {
                        self.symbols
                            .insert_import(symbol_name.as_ref(), version, *id)
                    }
                    _ => self.symbols.insert(symbol_name.as_ref(), version, *id),
                }
                .map_err(|_| ResolveError::DuplicateSymbol(symbol_name.clone()))?;
            }
        }

        // Finally we can build the actual nodes.
        for (id, node) in zip_eq(ids, nodes) {
            self.resolve_node(*id, node)?;
        }

        Ok(ids)
    }

    fn resolve_node(&mut self, node_id: NodeId, node: &'a Node) -> BuildResult<()> {
        let inputs = self.resolve_links(&node.inputs)?;
        let outputs = self.resolve_links(&node.outputs)?;

        // When the node introduces a symbol it also introduces a new variable scope.
        if node.operation.symbol().is_some() {
            self.vars.enter(node_id);
        }

        let mut scope_closure = ScopeClosure::Open;

        let operation = match &node.operation {
            Operation::Invalid => table::Operation::Invalid,
            Operation::Dfg => table::Operation::Dfg,
            Operation::Cfg => table::Operation::Cfg,
            Operation::Block => table::Operation::Block,
            Operation::TailLoop => table::Operation::TailLoop,
            Operation::Conditional => table::Operation::Conditional,
            Operation::DefineFunc(symbol) => {
                let symbol = self.resolve_symbol(symbol)?;
                scope_closure = ScopeClosure::Closed;
                table::Operation::DefineFunc(symbol)
            }
            Operation::DeclareFunc(symbol) => {
                let symbol = self.resolve_symbol(symbol)?;
                table::Operation::DeclareFunc(symbol)
            }
            Operation::DefineAlias(symbol, term) => {
                let symbol = self.resolve_symbol(symbol)?;
                let term = self.resolve_term(term)?;
                table::Operation::DefineAlias(symbol, term)
            }
            Operation::DeclareAlias(symbol) => {
                let symbol = self.resolve_symbol(symbol)?;
                table::Operation::DeclareAlias(symbol)
            }
            Operation::DeclareConstructor(symbol) => {
                let symbol = self.resolve_symbol(symbol)?;
                table::Operation::DeclareConstructor(symbol)
            }
            Operation::DeclareOperation(symbol) => {
                let symbol = self.resolve_symbol(symbol)?;
                table::Operation::DeclareOperation(symbol)
            }
            Operation::Import(symbol_ident) => table::Operation::Import {
                name: symbol_ident.name.as_ref(),
                version: &symbol_ident.version,
            },
            Operation::Custom(term) => {
                let term = self.resolve_term(term)?;
                table::Operation::Custom(term)
            }
        };

        let meta = self.resolve_terms(&node.meta)?;
        let regions = self.resolve_regions(&node.regions, scope_closure)?;

        let signature = match &node.signature {
            Some(signature) => Some(self.resolve_term(signature)?),
            None => None,
        };

        // We need to close the variable scope if we have opened one before.
        if node.operation.symbol().is_some() {
            self.vars.exit();
        }

        self.module.nodes[node_id.index()] = table::Node {
            operation,
            inputs,
            outputs,
            regions,
            meta,
            signature,
        };

        Ok(())
    }

    fn resolve_links(&mut self, links: &'a [LinkName]) -> BuildResult<&'a [LinkIndex]> {
        try_alloc_slice(self.bump, links.iter().map(|link| self.resolve_link(link)))
    }

    fn resolve_link(&mut self, link: &'a LinkName) -> BuildResult<LinkIndex> {
        Ok(self.links.use_link(link.as_ref()))
    }

    fn resolve_regions(
        &mut self,
        regions: &'a [Region],
        scope_closure: ScopeClosure,
    ) -> BuildResult<&'a [RegionId]> {
        try_alloc_slice(
            self.bump,
            regions
                .iter()
                .map(|region| self.resolve_region(region, scope_closure)),
        )
    }

    fn resolve_region(
        &mut self,
        region: &'a Region,
        scope_closure: ScopeClosure,
    ) -> BuildResult<RegionId> {
        let meta = self.resolve_terms(&region.meta)?;
        let signature = match &region.signature {
            Some(signature) => Some(self.resolve_term(signature)?),
            None => None,
        };

        // We insert a placeholder for the region in order to allocate a region
        // id, which we need to track the region's scopes.
        let region_id = self.module.insert_region(table::Region::default());

        // Each region defines a new scope for symbols.
        self.symbols.enter(region_id);

        // If the region is closed, it also defines a new scope for links.
        if ScopeClosure::Closed == scope_closure {
            self.links.enter(region_id);
        }

        let sources = self.resolve_links(&region.sources)?;
        let targets = self.resolve_links(&region.targets)?;
        let children = self.resolve_nodes(&region.children)?;

        // Close the region's scopes.
        let scope = match scope_closure {
            ScopeClosure::Open => None,
            ScopeClosure::Closed => {
                let (links, ports) = self.links.exit();
                Some(table::RegionScope { links, ports })
            }
        };
        self.symbols.exit();

        self.module.regions[region_id.index()] = table::Region {
            kind: region.kind,
            sources,
            targets,
            children,
            meta,
            signature,
            scope,
        };

        Ok(region_id)
    }

    fn resolve_symbol(&mut self, symbol: &'a Symbol) -> BuildResult<&'a table::Symbol<'a>> {
        let name = symbol.name.as_ref();
        let visibility = &symbol.visibility;
        let params = self.resolve_params(&symbol.params)?;
        let constraints = self.resolve_terms(&symbol.constraints)?;
        let signature = self.resolve_term(&symbol.signature)?;

        Ok(self.bump.alloc(table::Symbol {
            visibility,
            name,
            version: &symbol.version,
            params,
            constraints,
            signature,
        }))
    }

    /// Builds symbol parameters.
    ///
    /// This incrementally inserts the names of the parameters into the current
    /// variable scope, so that any parameter is in scope for each of its
    /// succeeding parameters.
    fn resolve_params(&mut self, params: &'a [Param]) -> BuildResult<&'a [table::Param<'a>]> {
        try_alloc_slice(
            self.bump,
            params.iter().map(|param| self.resolve_param(param)),
        )
    }

    /// Builds a symbol parameter.
    ///
    /// This inserts the name of the parameter into the current variable scope,
    /// making the parameter accessible as a variable.
    fn resolve_param(&mut self, param: &'a Param) -> BuildResult<table::Param<'a>> {
        let name = param.name.as_ref();
        let r#type = self.resolve_term(&param.r#type)?;

        self.vars
            .insert(param.name.as_ref())
            .map_err(|_| ResolveError::DuplicateVar(param.name.clone()))?;

        Ok(table::Param { name, r#type })
    }

    fn resolve_var(&self, var_name: &'a VarName) -> BuildResult<VarId> {
        self.vars
            .resolve(var_name.as_ref())
            .map_err(|_| ResolveError::UnknownVar(var_name.clone()))
    }

    /// Resolves a symbol identifier and returns the node that introduces it.
    ///
    /// Versioned references resolve exactly. Unversioned references first use
    /// any unversioned binding, then the latest visible versioned binding.
    /// If no binding exists, the implicitly created import preserves the
    /// reference version as written, including `None` for legacy unversioned
    /// references.
    ///
    /// TODO: Remove the legacy unversioned fallback once encoded HUGRs without
    /// extension version information are no longer supported.
    /// <http://github.com/Quantinuum/hugr/issues/3086>
    ///
    /// When there is no symbol with this name in scope, we create a new import
    /// node in the module and record that the symbol has been implicitly
    /// imported. At the end of the building process, these import nodes are
    /// inserted into the module's scope.
    fn resolve_symbol_ident(&mut self, symbol_ident: &'a SymbolIdent) -> NodeId {
        if let Ok(node) = self
            .symbols
            .resolve(symbol_ident.name.as_ref(), symbol_ident.version.as_ref())
        {
            return node;
        }

        *self.imports.entry(symbol_ident.clone()).or_insert_with(|| {
            self.module.insert_node(table::Node {
                operation: table::Operation::Import {
                    name: symbol_ident.name.as_ref(),
                    version: &symbol_ident.version,
                },
                ..Default::default()
            })
        })
    }

    pub fn finish(self) -> table::Module<'a> {
        self.module
    }
}

/// Error that may occur in [`Module::resolve`].
#[derive(Debug, Clone, Error)]
#[non_exhaustive]
#[error("Error resolving model module")]
pub enum ResolveError {
    /// Unknown variable.
    #[error("unknown var: {0}")]
    UnknownVar(VarName),
    /// Duplicate variable definition in the same symbol.
    #[error("duplicate var: {0}")]
    DuplicateVar(VarName),
    /// Duplicate symbol definition in the same region.
    #[error("duplicate symbol: {0}")]
    DuplicateSymbol(SymbolName),
}

type BuildResult<T> = Result<T, ResolveError>;

fn try_alloc_slice<T, E>(
    bump: &Bump,
    iter: impl IntoIterator<Item = Result<T, E>>,
) -> Result<&[T], E> {
    let iter = iter.into_iter();
    let mut vec = BumpVec::with_capacity_in(iter.size_hint().0, bump);
    for item in iter {
        vec.push(item?);
    }
    Ok(vec.into_bump_slice())
}

#[cfg(test)]
mod test {
    use crate::v0::{ast, table};
    use bumpalo::Bump;
    use rstest::rstest;
    use std::str::FromStr as _;

    #[derive(Debug, Clone, Copy)]
    enum SymbolUse {
        Custom,
        Meta(usize),
    }

    #[rstest]
    fn root_var_errors() {
        let text = "(hugr 0) (mod) (meta ?x)";
        let ast = ast::Package::from_str(text.trim()).unwrap();
        assert!(ast.resolve(&Bump::new()).is_err());
    }

    /// Unversioned extension uses resolve to declarations in scope.
    #[rstest]
    #[case::operation(
        "
            (hugr 0)
            (mod)
            (import someOp@0.2.3)
            (someOp)
            (declare-operation someOp@0.3.0 (core.fn [] []))
        ",
        SymbolUse::Custom,
        "someOp",
        Some("0.3.0")
    )]
    #[case::type_term(
        "
            (hugr 0)
            (mod)
            (meta someType)
            (import someType@0.2.3)
        ",
        SymbolUse::Meta(0),
        "someType",
        Some("0.2.3")
    )]
    #[case::type_latest(
        "
            (hugr 0)
            (mod)
            (meta someType)
            (import someType@0.2.3)
            (import someType@0.3.0)
        ",
        SymbolUse::Meta(0),
        "someType",
        Some("0.3.0")
    )]
    #[case::unversioned_import(
        "
            (hugr 0)
            (mod)
            (meta someType)
            (import someType)
        ",
        SymbolUse::Meta(0),
        "someType",
        None
    )]
    #[case::unversioned_operation(
        "
            (hugr 0)
            (mod)
            (someOp)
            (declare-operation someOp (core.fn [] []))
        ",
        SymbolUse::Custom,
        "someOp",
        None
    )]
    fn unversioned_resolution(
        #[case] text: &str,
        #[case] symbol_use: SymbolUse,
        #[case] expected_name: &str,
        #[case] expected_version: Option<&str>,
    ) {
        let bump = Bump::new();
        let ast = ast::Package::from_str(text.trim()).unwrap();
        let package = ast.resolve(&bump).unwrap();
        let module = &package.modules[0];

        assert_symbol_use(module, symbol_use, expected_name, expected_version);
    }

    fn assert_symbol_use(
        module: &table::Module<'_>,
        symbol_use: SymbolUse,
        expected_name: &str,
        expected_version: Option<&str>,
    ) {
        let term = match symbol_use {
            SymbolUse::Custom => custom_term(module),
            SymbolUse::Meta(index) => module.get_region(module.root).unwrap().meta[index],
        };

        assert_symbol_application(module, term, expected_name, expected_version);
    }

    fn custom_term(module: &table::Module<'_>) -> table::TermId {
        let root = module.get_region(module.root).unwrap();
        root.children
            .iter()
            .find_map(|node_id| {
                let node = module.get_node(*node_id).unwrap();
                match node.operation {
                    table::Operation::Custom(term) => Some(term),
                    _ => None,
                }
            })
            .expect("expected a custom operation node")
    }

    fn assert_symbol_application(
        module: &table::Module<'_>,
        term: table::TermId,
        expected_name: &str,
        expected_version: Option<&str>,
    ) {
        let table::Term::Apply(symbol, args) = module.get_term(term).unwrap() else {
            panic!("expected term to be a symbol application");
        };
        assert!(args.is_empty());

        let node = module.get_node(*symbol).unwrap();
        let name = node.operation.symbol().expect("expected symbol node");
        let version = node
            .operation
            .symbol_version()
            .expect("expected symbol version");
        assert_eq!(name, expected_name);
        assert_eq!(
            version.as_ref().map(ToString::to_string).as_deref(),
            expected_version
        );
    }
}
