//! Scope configuration for a pass.
//!
//! This defines the parts of the HUGR that a pass should be applied to, and
//! which parts is it allowed to modify.
//!
//! See [`PassScope`] for more details.

use hugr_core::ops::OpType;
use hugr_core::{HugrView, Node, Visibility};
use itertools::{Either, Itertools};

/// Scope configuration for a pass.
///
/// The scope of a pass defines which parts of a HUGR it is allowed to modify.
///
/// Each variant defines the following properties:
/// - `roots` is a set of **regions** in the HUGR that the pass should be
///   applied to.
///   - The pass **MUST NOT** modify the container nodes of the regions defined
///     in `roots`. This includes the optype and ports of the node.
/// - `scope` is a set of **nodes** in the HUGR that the pass **MAY** modify.
///   - This set is closed under descendants, meaning that all the descendants
///     of a node in `scope` are also in scope.
///   - Nodes that are not in `scope` **MUST** remain unchanged.
///   - Regions parents defined in `roots` are never in scope, as they should
///     not be modified.
///   - The entrypoint node is never in scope.
/// - `recursive` is a boolean flag indicating whether the pass **SHOULD**
///   optimize the descendants of the regions in `roots`.
///   - If this flag is `false`, the pass **MAY** still modify the descendant
///     regions.
///
/// A pass will always optimize the entrypoint region, unless it is set to the
/// module root.
//
// This enum should be kept in sync with the `PassScope` enum in `hugr-py`.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Default, derive_more::Display)]
#[non_exhaustive]
pub enum PassScope {
    /// Run the pass only on the entrypoint region.
    ///
    /// - `roots`: The entrypoint node, if it is not the module root.
    /// - `scope`: The descendants of the entrypoint node, if `entrypoint` is
    ///   not the module root.
    /// - `recursive`: `false`.
    EntrypointFlat,
    /// Run the pass on the entrypoint region and all its descendants.
    ///
    /// - `roots`: The entrypoint node, if it is not the module root.
    /// - `scope`: The descendants of the entrypoint node, if `entrypoint` is
    ///   not the module root.
    /// - `recursive`: `true`.
    EntrypointRecursive,
    /// Run the pass on all regions and nodes in the Hugr.
    ///
    /// - `roots`: Every function defined in the module.
    /// - `scope`: The whole Hugr, except nodes in the module root region and
    ///   the entrypoint node.
    /// - `recursive`: `true`.
    All,
    /// Run the pass on all public functions in the Hugr.
    ///
    /// Private functions and constant definitions may be modified, or even
    /// removed, by the pass.
    ///
    /// - `roots`: Every public function defined in the module.
    /// - `scope`: The whole Hugr, except public function definitions and
    ///   declarations in the module root and the entrypoint node.
    /// - `recursive`: `true`.
    #[default]
    AllPublic,
}

impl PassScope {
    /// Returns the root nodes to be optimized by the pass.
    ///
    /// These are the root regions that the pass should be applied to. If
    /// [`PassScope::recursive`] is `true`, the descendants of the root regions
    /// should also be optimized.
    pub fn roots<'a, H: HugrView<Node = Node>>(
        &'a self,
        hugr: &'a H,
    ) -> impl Iterator<Item = H::Node> {
        match self {
            Self::EntrypointFlat | Self::EntrypointRecursive => {
                // Include the entrypoint if it is not the module root.
                let module_root = hugr.module_root();
                let entrypoint =
                    std::iter::once(hugr.entrypoint()).filter(move |node| *node != module_root);

                Either::Left(entrypoint)
            }
            Self::All | Self::AllPublic => {
                // Decide which public functions to include.
                let functions = hugr.children(hugr.module_root()).filter(move |&node| {
                    let Some(fn_op) = hugr.get_optype(node).as_func_defn() else {
                        return false;
                    };
                    let public = fn_op.visibility() == &Visibility::Public;
                    match self {
                        Self::All => true,
                        Self::AllPublic => public,
                        _ => unreachable!(),
                    }
                });

                Either::Right(functions)
            }
        }
    }

    /// Return every region in the Hugr to be optimized by the pass.
    ///
    /// This computes all the regions to be optimized at once. In general, it is
    /// more efficient to traverse the Hugr incrementally starting from
    /// [PassScope::roots] instead.
    pub fn regions<'a, H: HugrView<Node = Node>>(&'a self, hugr: &'a H) -> Vec<H::Node> {
        let mut regions = self.roots(hugr).collect_vec();

        if self.recursive() {
            let mut index = 0;
            while index < regions.len() {
                let region = regions[index];
                let child_regions = hugr
                    .children(region)
                    .filter(|&child| hugr.first_child(child).is_some());
                regions.extend(child_regions);
                index += 1;
            }
        }

        regions
    }

    /// Returns `true` if the node may be modified by the pass.
    ///
    /// Nodes in `root` are never in scope, but their children will be.
    ///
    /// If [PassScope::recursive] is `true`, then all descendants of nodes in
    /// `root` are also in scope.
    ///
    /// Other nodes may also be in scope, as listed in the definition of the
    /// [PassScope] variant.
    pub fn in_scope<H: HugrView<Node = Node>>(&self, hugr: &H, node: H::Node) -> bool {
        // The root module node is never in scope.
        let Some(node_parent) = hugr.get_parent(node) else {
            return false;
        };
        // The entrypoint node is never in scope.
        if node == hugr.entrypoint() {
            return false;
        }

        match self {
            Self::EntrypointFlat | Self::EntrypointRecursive => {
                if hugr.entrypoint() == hugr.module_root() {
                    return false;
                }
                // The node is in scope if one of its ancestors is the entrypoint.
                std::iter::successors(hugr.get_parent(node), |node| hugr.get_parent(*node))
                    .contains(&hugr.entrypoint())
            }
            Self::All => {
                // Any node not in the module root is in scope.
                node_parent != hugr.module_root()
            }
            Self::AllPublic => {
                if node_parent != hugr.module_root() {
                    return true;
                }
                // For module children, only private functions
                // declarations/definitions and const are in scope.
                match hugr.get_optype(node) {
                    OpType::FuncDefn(func) => func.visibility() != &Visibility::Public,
                    OpType::FuncDecl(func) => func.visibility() != &Visibility::Public,
                    _ => true,
                }
            }
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
    use hugr_core::hugr::hugrmut::HugrMut;
    use rstest::{fixture, rstest};

    use hugr_core::Hugr;
    use hugr_core::builder::{Container, Dataflow, HugrBuilder, ModuleBuilder, SubContainer};
    use hugr_core::ops::Value;
    use hugr_core::ops::handle::NodeHandle;
    use hugr_core::std_extensions::arithmetic::int_types::ConstInt;
    use hugr_core::types::Signature;

    use super::*;

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
        assert_eq!(scope.roots(&hugr.hugr).collect_vec(), vec![]);
        assert_eq!(scope.regions(&hugr.hugr), vec![]);
        assert!(!scope.in_scope(&hugr.hugr, hugr.module_root));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func_nested));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.const_def));

        // Public function with a nested DFG
        hugr.hugr.set_entrypoint(hugr.public_func);
        assert_eq!(
            scope.roots(&hugr.hugr).collect_vec(),
            vec![hugr.public_func]
        );
        match recursive {
            true => assert_eq!(
                scope.regions(&hugr.hugr),
                vec![hugr.public_func, hugr.public_func_nested]
            ),
            false => assert_eq!(scope.regions(&hugr.hugr), vec![hugr.public_func]),
        }
        assert!(!scope.in_scope(&hugr.hugr, hugr.module_root));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func));
        assert!(scope.in_scope(&hugr.hugr, hugr.public_func_nested));
        assert!(!scope.in_scope(&hugr.hugr, hugr.module_root));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.const_def));

        // DFG inside a function
        hugr.hugr.set_entrypoint(hugr.public_func_nested);
        assert_eq!(
            scope.roots(&hugr.hugr).collect_vec(),
            vec![hugr.public_func_nested]
        );
        assert_eq!(scope.regions(&hugr.hugr), vec![hugr.public_func_nested]);
        assert!(!scope.in_scope(&hugr.hugr, hugr.module_root));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func_nested));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.const_def));
    }

    #[rstest]
    fn scope_all(hugr: TestHugr) {
        let scope = PassScope::All;
        assert!(scope.recursive());

        assert_eq!(
            scope.roots(&hugr.hugr).collect_vec(),
            vec![hugr.public_func, hugr.private_func]
        );
        assert_eq!(
            scope.regions(&hugr.hugr),
            vec![hugr.public_func, hugr.private_func, hugr.public_func_nested]
        );
        assert!(!scope.in_scope(&hugr.hugr, hugr.module_root));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func));
        assert!(scope.in_scope(&hugr.hugr, hugr.public_func_nested));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.private_func_decl));
        assert!(!scope.in_scope(&hugr.hugr, hugr.const_def));
    }

    #[rstest]
    fn scope_all_public(hugr: TestHugr) {
        let scope = PassScope::AllPublic;
        assert!(scope.recursive());

        assert_eq!(
            scope.roots(&hugr.hugr).collect_vec(),
            vec![hugr.public_func]
        );
        assert_eq!(
            scope.regions(&hugr.hugr),
            vec![hugr.public_func, hugr.public_func_nested]
        );
        assert!(!scope.in_scope(&hugr.hugr, hugr.module_root));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func));
        assert!(scope.in_scope(&hugr.hugr, hugr.public_func_nested));
        assert!(scope.in_scope(&hugr.hugr, hugr.private_func));
        assert!(!scope.in_scope(&hugr.hugr, hugr.public_func_decl));
        assert!(scope.in_scope(&hugr.hugr, hugr.private_func_decl));
        assert!(scope.in_scope(&hugr.hugr, hugr.const_def));
    }
}
