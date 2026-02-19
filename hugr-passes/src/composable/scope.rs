//! Scope configuration for a pass.
//!
//! This defines the parts of the HUGR that a pass should be applied to, and
//! which parts is it allowed to modify.
//!
//! See [`PassScope`] for more details.

use hugr_core::ops::{OpType, ValidateOp};
use hugr_core::{HugrView, Visibility};
use itertools::{Either, Itertools};

/// Scope configuration for a pass.
///
/// The scope of a pass defines which parts of a HUGR it is allowed to modify.
///
/// Each variant defines three properties: [PassScope::root],
/// [PassScope::preserve_interface], and [PassScope::recursive].
///
/// From these, [PassScope::regions] and [PassScope::in_scope] can be derived.
///
/// A pass will always optimize the entrypoint region, unless it is set to the
/// module root.
//
// This enum should be kept in sync with the `PassScope` enum in `hugr-py`.
#[derive(Debug, Clone, PartialEq, Eq, derive_more::From, Hash, derive_more::Display)]
#[non_exhaustive]
pub enum PassScope {
    /// Run the pass only on the entrypoint region.
    ///
    /// If the entrypoint is the module root, does nothing.
    ///
    /// The pass is allowed, but not required, to optimize descendant regions too.
    ///
    /// - `root`: The entrypoint node, if it is not the module root.
    /// - `preserve_interface`: the entrypoint node
    /// - `recursive`: `false`.
    EntrypointFlat,
    /// Run the pass on the entrypoint region and all its descendants.
    ///
    /// For an idempotent pass, this means that immediately rerunning the pass on
    /// any subregion (i.e. with the entrypoint set to any descendant of
    /// the current value), must have no effect.
    ///
    /// If the entrypoint is the module root, does nothing.
    ///
    /// - `root`: The entrypoint node, if it is not the module root.
    /// - `preserve_interface`: the entrypoint node
    /// - `recursive`: `true`.
    EntrypointRecursive,
    /// Run the pass on the whole Hugr, regardless of the entrypoint.
    ///
    /// For lowering passes, signature changes etc. should be applied across the hugr.
    ///
    /// For optimization passes, the inner [Preservation] details which parts must
    /// have their interface preserved.
    ///
    /// - `root`: the [HugrView::module_root]
    /// - `preserve_interface`: according to [Preservation]
    /// - `recursive`: `true`.
    Global(#[from] Preserve),
}

/// What part of the Hugr should have its interface preserved by optimization passes.
///
/// (Interface means signature/value ports, as well as static ports, and their types;
/// also name (if public) for linking; and whether the node is a valid dataflow child
/// or is a [DataflowBlock], [ExitBlock] or [Module]).
///
/// [DataflowBlock]: OpType::DataflowBlock
/// [ExitBlock]: OpType::ExitBlock
/// [Module]: OpType::Module
#[derive(Debug, Clone, PartialEq, Eq, Default, Hash, derive_more::Display)]
pub enum Preserve {
    /// Optimization passes must preserve behaviour and interface of every
    /// module child, as well as the entrypoint.
    ///
    /// `preserve_interface`: every child of the module, and the entrypoint.
    All,
    /// Optimization passes must preserve interface and behaviour of all public
    /// functions, as well as the entrypoint.
    ///
    /// Private functions and constant definitions may be modified, including
    /// changing their behaviour or deleting them entirely, so long as this
    /// does not affect behaviour of the public functions (or entrypoint).
    ///
    /// - `preserve_interface`: every public function defined in the module,
    ///   and the entrypoint.
    #[default]
    Public,
    /// Run the pass on the whole Hugr, but preserving behaviour only of the entrypoint.
    ///
    /// If the entrypoint is the module root, then the same as [Self::Public].
    // ALAN could be Self::All in such case, but if so then Self::Public
    // with entrypoint==module_root should also be equivalent to Self::All, so no.
    ///
    /// - `preserve_interface`: if the entrypoint node is the module root, then all
    ///   children of the module root; otherwise, just the entrypoint node.
    Entrypoint,
}

impl Default for PassScope {
    fn default() -> Self {
        Self::Global(Preserve::default())
    }
}

/// Whether a pass may modify a particular node
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum InScope {
    /// The pass may modify the node arbitrarily, including changing its interface,
    /// behaviour, and/or removing it altogether
    Yes,
    /// The pass may modify the interior of the node - its [OpType], and its descendants -
    /// but must maintain the same ports (including static [Function] ports and [ControlFlow] ports),
    /// function name and [Visibility], and behaviour.
    ///
    /// [Function]: [hugr_core::types::EdgeKind::Function]
    /// [ControlFlow]: [EdgeKind::ControlFlow]
    PreserveInterface,
    /// The pass may not modify this node
    No,
}

impl PassScope {
    /// Returns a scope that covers (only) the entrypoint subtree of the specified Hugr.
    ///
    /// Handles module-rooted Hugrs (via [Self::PreserveAll]).
    pub fn from_entrypoint(h: &impl HugrView) -> Self {
        if h.entrypoint() == h.module_root() {
            // EntrypointXX say not to do anything in this case, so pick a global pass (rather arbitrarily)
            Self::Global(Preserve::All) // ALAN or default?
        } else {
            Self::EntrypointRecursive
        }
    }

    /// Returns the root of the subtree that may be optimized by the pass.
    ///
    /// If `None`, the pass may not do anything. (This can be the case for some
    /// entrypoint-specific scopes when the entrypoint is the module root. Use a global
    /// scope, e.g. [PassScope::PreserveAll] or [PassScope::PreservePublic], instead.)
    ///
    /// Otherwise, will be either the module root (for a global pass) or the entrypoint.
    ///
    /// The pass should not touch anything outside this root, must respect
    /// [Self::preserve_interface] within it, and if [`Self::recursive`]
    ///  is `true`, should also optimize the descendant regions of the root.
    pub fn root<'a, H: HugrView>(&'a self, hugr: &'a H) -> Option<H::Node> {
        let ep = hugr.entrypoint();
        match self {
            Self::EntrypointFlat | Self::EntrypointRecursive => {
                (ep != hugr.module_root()).then_some(ep)
            }
            Self::Global(_) => Some(hugr.module_root()),
        }
    }

    /// Returns a list of nodes, in the subtree beneath [Self::root], for which
    /// the pass must preserve the observable semantics (ports, execution behaviour,
    /// linking).
    ///
    /// We include the [Module] in this list (if it is [Self::root]) as these
    /// properties must be preserved (such rules out any other changes).
    ///
    /// [Module]: OpType::Module
    pub fn preserve_interface<'a, H: HugrView>(
        &'a self,
        hugr: &'a H,
    ) -> impl Iterator<Item = H::Node> + 'a {
        self.root(hugr).into_iter().flat_map(move |r| {
            let ep = hugr.entrypoint();
            [r, ep]
                .into_iter()
                .unique()
                .chain(hugr.children(hugr.module_root()).filter(move |n| {
                    if *n == ep {
                        return false; // Entrypoint added above
                    };
                    match self {
                        Self::Global(Preserve::All) => return true,
                        Self::Global(Preserve::Public) => (), // fallthrough
                        Self::Global(Preserve::Entrypoint) if ep == hugr.module_root() => (), // fallthough
                        _ => return false,
                    };
                    let vis = match hugr.get_optype(*n) {
                        OpType::FuncDecl(fd) => fd.visibility(),
                        OpType::FuncDefn(fd) => fd.visibility(),
                        _ => return false,
                    };
                    vis == &Visibility::Public
                }))
        })
    }

    /// Return every region (every [dataflow] or [CFG] container - but excluding
    /// [Module]) in the Hugr to be optimized by the pass.
    ///
    /// This computes all the regions to be optimized at once. In general, it is
    /// more efficient to traverse the Hugr incrementally starting from
    /// [PassScope::root] instead.
    ///
    /// [dataflow]: hugr_core::ops::OpTag::DataflowParent
    /// [CFG]: OpType::CFG
    /// [Module]: OpType::Module
    pub fn regions<'a, H: HugrView>(&'a self, hugr: &'a H) -> impl Iterator<Item = H::Node> {
        self.root(hugr).into_iter().flat_map(|r| {
            if self.recursive() {
                let mut iter = hugr.descendants(r);
                if r == hugr.module_root() {
                    assert_eq!(iter.next(), Some(hugr.module_root())); // skip
                }
                Either::Left(iter.filter(|n| {
                    hugr.get_optype(*n)
                        .validity_flags::<H::Node>()
                        .requires_children
                }))
            } else {
                assert_ne!(r, hugr.module_root());
                Either::Right(std::iter::once(r))
            }
        })
    }

    /// Returns whether the node may be modified by the pass.
    ///
    /// Nodes outside the `root` subtree are never in scope.
    /// Nodes inside the subtree may be either [InScope::Yes] or [InScope::PreserveInterface].
    pub fn in_scope<H: HugrView>(&self, hugr: &H, node: H::Node) -> InScope {
        // The root module node is never in scope.
        if node == hugr.module_root() {
            return InScope::No;
        };
        let Some(r) = self.root(hugr) else {
            return InScope::No;
        };
        'in_subtree: {
            if r != hugr.module_root() {
                let mut anc = Some(node);
                while let Some(n) = anc {
                    if n == r {
                        break 'in_subtree;
                    };
                    anc = hugr.get_parent(n);
                }
                return InScope::No;
            }
        }
        if self.preserve_interface(hugr).contains(&node) {
            InScope::PreserveInterface
        } else {
            InScope::Yes
        }
    }

    /// Returns `true` if the pass should be applied recursively on the
    /// descendants of the root regions.
    pub fn recursive(&self) -> bool {
        !matches!(self, Self::EntrypointFlat)
    }
}

#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use hugr_core::hugr::hugrmut::HugrMut;
    use rstest::{fixture, rstest};

    use hugr_core::builder::{Container, Dataflow, HugrBuilder, ModuleBuilder, SubContainer};
    use hugr_core::ops::Value;
    use hugr_core::ops::handle::NodeHandle;
    use hugr_core::std_extensions::arithmetic::int_types::ConstInt;
    use hugr_core::types::Signature;
    use hugr_core::{Hugr, Node};

    use super::*;

    #[derive(Debug)]
    struct TestHugr {
        hugr: Hugr,
        module_root: Node,
        public_func: Node,
        public_func_nested: Node,
        private_func: Node,
        public_func_decl: Node,
        private_func_decl: Node,
        const_def: Node,
    }

    #[fixture]
    fn hugr() -> TestHugr {
        let mut h = ModuleBuilder::new();
        let module_root = h.container_node();

        let (public_func, public_func_nested) = {
            let mut pub_f = h
                .define_function_vis(
                    "public_func",
                    Signature::new_endo(vec![]),
                    Visibility::Public,
                )
                .unwrap();

            let public_func_nested = {
                let pub_f_nested = pub_f.dfg_builder(Signature::new_endo(vec![]), []).unwrap();
                pub_f_nested.finish_sub_container().unwrap().node()
            };

            (
                pub_f.finish_sub_container().unwrap().node(),
                public_func_nested,
            )
        };

        let private_func = {
            let priv_f = h
                .define_function_vis(
                    "private_func",
                    Signature::new_endo(vec![]),
                    Visibility::Private,
                )
                .unwrap();
            priv_f.finish_sub_container().unwrap().node()
        };

        let public_func_decl = h
            .declare_vis(
                "public_func_decl",
                Signature::new_endo(vec![]).into(),
                Visibility::Public,
            )
            .unwrap()
            .node();

        let private_func_decl = h
            .declare_vis(
                "private_func_decl",
                Signature::new_endo(vec![]).into(),
                Visibility::Private,
            )
            .unwrap()
            .node();

        let const_def = h
            .add_constant(Value::from(ConstInt::new_u(5, 7).unwrap()))
            .node();

        TestHugr {
            hugr: h.finish_hugr().unwrap(),
            module_root,
            public_func,
            public_func_nested,
            private_func,
            public_func_decl,
            private_func_decl,
            const_def,
        }
    }

    #[rstest]
    #[case(PassScope::EntrypointFlat, false)]
    #[case(PassScope::EntrypointRecursive, true)]
    fn scope_entrypoint(mut hugr: TestHugr, #[case] scope: PassScope, #[case] recursive: bool) {
        assert_eq!(scope.recursive(), recursive);

        // When the entrypoint is the module root,
        // the pass should not be applied to any regions.
        hugr.hugr.set_entrypoint(hugr.module_root);
        assert_eq!(scope.root(&hugr.hugr), None);
        assert_eq!(scope.regions(&hugr.hugr).next(), None);
        for n in hugr.hugr.nodes() {
            assert_eq!(scope.in_scope(&hugr.hugr, n), InScope::No);
        }

        // Public function with a nested DFG
        hugr.hugr.set_entrypoint(hugr.public_func);
        assert_eq!(scope.root(&hugr.hugr), Some(hugr.public_func));
        let expected_regions = match recursive {
            true => vec![hugr.public_func, hugr.public_func_nested],
            false => vec![hugr.public_func],
        };
        assert_eq!(scope.regions(&hugr.hugr).collect_vec(), expected_regions);

        assert_eq!(scope.in_scope(&hugr.hugr, hugr.module_root), InScope::No);
        assert_eq!(
            scope.in_scope(&hugr.hugr, hugr.public_func),
            InScope::PreserveInterface
        );
        assert_eq!(
            scope.in_scope(&hugr.hugr, hugr.public_func_nested),
            InScope::Yes
        );
        for n in [
            hugr.module_root,
            hugr.private_func,
            hugr.public_func_decl,
            hugr.private_func_decl,
            hugr.const_def,
        ] {
            assert_eq!(scope.in_scope(&hugr.hugr, n), InScope::No);
        }

        // DFG inside a function
        hugr.hugr.set_entrypoint(hugr.public_func_nested);
        assert_eq!(scope.root(&hugr.hugr), Some(hugr.public_func_nested));
        assert_eq!(
            scope.regions(&hugr.hugr).collect_vec(),
            [hugr.public_func_nested]
        );
        for n in [
            hugr.module_root,
            hugr.public_func,
            hugr.private_func,
            hugr.public_func_decl,
            hugr.private_func_decl,
            hugr.const_def,
        ] {
            assert_eq!(scope.in_scope(&hugr.hugr, n), InScope::No)
        }
        assert_eq!(
            scope.in_scope(&hugr.hugr, hugr.public_func_nested),
            InScope::PreserveInterface
        );
    }

    #[rstest]
    fn scope_all(hugr: TestHugr) {
        let preserve = [
            hugr.public_func,
            hugr.private_func,
            hugr.public_func_decl,
            hugr.private_func_decl,
            hugr.const_def,
        ];
        scope_preserve(&hugr, &PassScope::Global(Preserve::All), preserve)
    }

    fn scope_preserve(
        hugr: &TestHugr,
        scope: &PassScope,
        preserve_chs: impl IntoIterator<Item = Node>,
    ) {
        assert!(scope.recursive());
        let preserve = preserve_chs.into_iter().collect::<HashSet<_>>();
        assert_eq!(scope.root(&hugr.hugr), Some(hugr.module_root));
        assert_eq!(
            scope.regions(&hugr.hugr).collect_vec(),
            [hugr.public_func, hugr.private_func, hugr.public_func_nested]
        );
        assert_eq!(scope.in_scope(&hugr.hugr, hugr.module_root), InScope::No);
        for n in [
            hugr.public_func,
            hugr.private_func,
            hugr.public_func_decl,
            hugr.public_func_nested,
            hugr.private_func_decl,
            hugr.const_def,
        ] {
            let expected = if preserve.contains(&n) {
                InScope::PreserveInterface
            } else {
                InScope::Yes
            };
            assert_eq!(scope.in_scope(&hugr.hugr, n), expected, "{:?} among {:?}", n, hugr);
        }
        let mut preserve = preserve;
        preserve.insert(hugr.module_root);
        assert_eq!(preserve, scope.preserve_interface(&hugr.hugr).collect());
    }

    #[rstest]
    fn scope_all_public(hugr: TestHugr) {
        let preserve = [hugr.public_func, hugr.public_func_decl];
        scope_preserve(&hugr, &PassScope::Global(Preserve::Public), preserve)
    }

    #[rstest]
    fn scope_global_entrypoint(mut hugr: TestHugr) {
        let scope = &PassScope::Global(Preserve::Entrypoint);
        hugr.hugr.set_entrypoint(hugr.hugr.module_root());
        let preserve = [hugr.public_func, hugr.public_func_decl];
        scope_preserve(&hugr, scope, preserve);

        hugr.hugr.set_entrypoint(hugr.public_func_nested);
        let preserve = [hugr.public_func_nested];
        scope_preserve(&hugr, scope, preserve)
    }
}
