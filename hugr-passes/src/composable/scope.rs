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
/// The scope of a pass defines which parts of a HUGR it should be applied to,
/// and which parts it is allowed to modify.
///
/// Each variant defines three properties: [PassScope::root],
/// [PassScope::preserve_interface], and [PassScope::recursive].
///
/// From these, [PassScope::regions] and [PassScope::in_scope] can be derived.
///
/// A pass will always optimize the entrypoint region, unless the entrypoint
/// is the module root.
//
// This enum should be kept in sync with the `PassScope` enum in `hugr-py`.
#[derive(Debug, Clone, PartialEq, Eq, derive_more::From, Hash, derive_more::Display)]
#[non_exhaustive]
pub enum PassScope {
    /// Run the pass on the entrypoint region.
    ///
    /// If the entrypoint is the module root, does nothing.
    ///
    /// The pass is allowed, but not required, to optimize descendant regions too.
    /// (For passes where it makes sense to distinguish flat from [Self::EntrypointRecursive],
    /// this is encouraged, but for many passes it does not make sense so both EntrypointXXX
    /// variants may behave the same.)
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
    /// For optimization passes, the inner [Preserve] details which parts must
    /// have their interface preserved.
    ///
    /// - `root`: the [HugrView::module_root]
    /// - `preserve_interface`: according to [Preserve]
    /// - `recursive`: `true`.
    Global(#[from] Preserve),
}

/// Which nodes in the Hugr should have their interface preserved by optimization passes.
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
    /// Thus, appropriate for a Hugr that will be linked as a library.
    ///
    /// - `preserve_interface`: every public function defined in the module,
    ///   and the entrypoint.
    #[default]
    Public,
    /// Run the pass on the whole Hugr, but preserving behaviour only of the entrypoint.
    ///
    /// Thus, appropriate for a Hugr that will be run as an executable, with the
    /// entrypoint indicating where execution will begin.
    ///
    /// If the entrypoint is the module root, then the same as [Self::Public].
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
    /// function name and [Visibility], and behaviour. For the [Module], this is equivalent
    /// to [InScope::No].
    ///
    /// [Function]: [hugr_core::types::EdgeKind::Function]
    /// [ControlFlow]: [EdgeKind::ControlFlow]
    /// [Module]: OpType::Module
    PreserveInterface,
    /// The pass may not modify this node
    No,
}

impl PassScope {
    /// Returns the root of the subtree that may be optimized by the pass.
    ///
    /// If `None`, the pass may not do anything. (This can be the case for some
    /// entrypoint-specific scopes when the entrypoint is the module root. Use
    /// [PassScope::Global] instead.)
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
    /// properties must be preserved (this rules out any other changes).
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
    /// more efficient to traverse the Hugr incrementally starting from the
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
    fn th() -> TestHugr {
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
    fn scope_entrypoint(mut th: TestHugr, #[case] scope: PassScope, #[case] recursive: bool) {
        assert_eq!(scope.recursive(), recursive);

        // When the entrypoint is the module root,
        // the pass should not be applied to any regions.
        th.hugr.set_entrypoint(th.module_root);
        assert_eq!(scope.root(&th.hugr), None);
        assert_eq!(scope.regions(&th.hugr).next(), None);
        for n in th.hugr.nodes() {
            assert_eq!(scope.in_scope(&th.hugr, n), InScope::No);
        }

        // Public function with a nested DFG
        th.hugr.set_entrypoint(th.public_func);
        assert_eq!(scope.root(&th.hugr), Some(th.public_func));
        let expected_regions = match recursive {
            true => vec![th.public_func, th.public_func_nested],
            false => vec![th.public_func],
        };
        assert_eq!(scope.regions(&th.hugr).collect_vec(), expected_regions);

        assert_eq!(scope.in_scope(&th.hugr, th.module_root), InScope::No);
        assert_eq!(
            scope.in_scope(&th.hugr, th.public_func),
            InScope::PreserveInterface
        );
        assert_eq!(
            scope.in_scope(&th.hugr, th.public_func_nested),
            InScope::Yes
        );
        for n in [
            th.module_root,
            th.private_func,
            th.public_func_decl,
            th.private_func_decl,
            th.const_def,
        ] {
            assert_eq!(scope.in_scope(&th.hugr, n), InScope::No);
        }

        // DFG inside a function
        th.hugr.set_entrypoint(th.public_func_nested);
        assert_eq!(scope.root(&th.hugr), Some(th.public_func_nested));
        assert_eq!(
            scope.regions(&th.hugr).collect_vec(),
            [th.public_func_nested]
        );
        for n in [
            th.module_root,
            th.public_func,
            th.private_func,
            th.public_func_decl,
            th.private_func_decl,
            th.const_def,
        ] {
            assert_eq!(scope.in_scope(&th.hugr, n), InScope::No)
        }
        assert_eq!(
            scope.in_scope(&th.hugr, th.public_func_nested),
            InScope::PreserveInterface
        );
    }

    #[rstest]
    fn preserve_all(th: TestHugr) {
        let preserve = [
            th.public_func,
            th.private_func,
            th.public_func_decl,
            th.private_func_decl,
            th.const_def,
        ];
        check_preserve(&th, Preserve::All, preserve)
    }

    fn check_preserve(
        th: &TestHugr,
        preserve: Preserve,
        expected_chs: impl IntoIterator<Item = Node>,
    ) {
        let scope = PassScope::Global(preserve);
        assert!(scope.recursive());
        let expected_chs = expected_chs.into_iter().collect::<HashSet<_>>();
        assert_eq!(scope.root(&th.hugr), Some(th.module_root));
        assert_eq!(
            scope.regions(&th.hugr).collect_vec(),
            [th.public_func, th.private_func, th.public_func_nested]
        );
        assert_eq!(
            scope.in_scope(&th.hugr, th.module_root),
            InScope::PreserveInterface
        );
        for n in [
            th.public_func,
            th.private_func,
            th.public_func_decl,
            th.public_func_nested,
            th.private_func_decl,
            th.const_def,
        ] {
            let expected = if expected_chs.contains(&n) {
                InScope::PreserveInterface
            } else {
                InScope::Yes
            };
            assert_eq!(
                scope.in_scope(&th.hugr, n),
                expected,
                "{:?} among {:?}",
                n,
                th
            );
        }
        let mut preserve = expected_chs;
        preserve.insert(th.module_root);
        assert_eq!(preserve, scope.preserve_interface(&th.hugr).collect());
    }

    #[rstest]
    fn preserve_public(th: TestHugr) {
        let preserve = [th.public_func, th.public_func_decl];
        check_preserve(&th, Preserve::Public, preserve)
    }

    #[rstest]
    fn preserve_entrypoint(mut th: TestHugr) {
        th.hugr.set_entrypoint(th.hugr.module_root());
        let preserve = [th.public_func, th.public_func_decl];
        check_preserve(&th, Preserve::Entrypoint, preserve);

        th.hugr.set_entrypoint(th.public_func_nested);
        let preserve = [th.public_func_nested];
        check_preserve(&th, Preserve::Entrypoint, preserve)
    }
}
