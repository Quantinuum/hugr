//! Pass for removing statically-unreachable functions from a Hugr

use std::collections::HashSet;

use hugr_core::{
    HugrView, Node, Visibility,
    hugr::hugrmut::HugrMut,
    module_graph::{ModuleGraph, StaticNode},
    ops::{OpTag, OpTrait},
};
use itertools::Either;
use petgraph::visit::{Dfs, Walker};

use crate::{
    ComposablePass, PassScope,
    composable::{ValidatePassError, validate_if_test},
};

#[derive(Debug, thiserror::Error)]
#[non_exhaustive]
/// Errors produced by [`RemoveDeadFuncsPass`].
pub enum RemoveDeadFuncsError<N = Node> {
    /// The specified entry point is not a `FuncDefn` node
    #[error(
        "Entrypoint for RemoveDeadFuncsPass {node} was not a function definition in the root module"
    )]
    InvalidEntryPoint {
        /// The invalid node.
        node: N,
    },
}

fn reachable_funcs<'a, H: HugrView>(
    cg: &'a ModuleGraph<H::Node>,
    h: &'a H,
    entry_points: impl IntoIterator<Item = H::Node>,
) -> impl Iterator<Item = H::Node> + 'a {
    let g = cg.graph();
    let mut d = Dfs::new(g, 0.into());
    d.stack.clear(); // Remove the fake 0
    for n in entry_points {
        d.stack.push(cg.node_index(n).unwrap());
    }
    d.iter(g).filter_map(|i| match g.node_weight(i).unwrap() {
        StaticNode::FuncDefn(n) | StaticNode::FuncDecl(n) => Some(*n),
        StaticNode::NonFuncEntrypoint => Some(h.entrypoint()),
        StaticNode::Const(_) => None,
        _ => unreachable!(),
    })
}

#[derive(Debug, Clone)]
/// A configuration for the Dead Function Removal pass.
pub struct RemoveDeadFuncsPass {
    entry_points: Either<Vec<Node>, PassScope>,
}

impl Default for RemoveDeadFuncsPass {
    fn default() -> Self {
        Self {
            entry_points: Either::Left(Vec::new()),
        }
    }
}

impl RemoveDeadFuncsPass {
    #[deprecated(note = "Use RemoveDeadFuncsPass::with_scope")]
    /// Adds new entry points - these must be [`FuncDefn`] nodes
    /// that are children of the [`Module`] at the root of the Hugr.
    ///
    /// Overrides any [PassScope] set by a call to [Self::with_scope].
    ///
    /// [`FuncDefn`]: hugr_core::ops::OpType::FuncDefn
    /// [`Module`]: hugr_core::ops::OpType::Module
    pub fn with_module_entry_points(
        mut self,
        entry_points: impl IntoIterator<Item = Node>,
    ) -> Self {
        let v = match self.entry_points {
            Either::Left(ref mut v) => v,
            Either::Right(_) => {
                self.entry_points = Either::Left(Vec::new());
                self.entry_points.as_mut().unwrap_left()
            }
        };
        v.extend(entry_points);
        self
    }
}

impl<H: HugrMut<Node = Node>> ComposablePass<H> for RemoveDeadFuncsPass {
    type Error = RemoveDeadFuncsError;
    type Result = ();

    /// Overrides any entrypoints set by a call to [Self::with_module_entry_points].
    fn with_scope(mut self, scope: &PassScope) -> Self {
        self.entry_points = Either::Right(scope.clone());
        self
    }

    fn run(&self, hugr: &mut H) -> Result<(), RemoveDeadFuncsError> {
        let mut entry_points = Vec::new();
        match &self.entry_points {
            Either::Left(ep) => {
                for &n in ep {
                    if !hugr.get_optype(n).is_func_defn() {
                        return Err(RemoveDeadFuncsError::InvalidEntryPoint { node: n });
                    }
                    debug_assert_eq!(hugr.get_parent(n), Some(hugr.module_root()));
                    entry_points.push(n);
                }
                if hugr.entrypoint() != hugr.module_root() {
                    entry_points.push(hugr.entrypoint())
                }
            }
            Either::Right(PassScope::EntrypointFlat | PassScope::EntrypointRecursive) => {
                // If the entrypoint is the module root, not allowed to touch anything.
                // Otherwise, we must keep the entrypoint (and can touch only inside it).
                return Ok(());
            }
            Either::Right(PassScope::PreserveAll) => return Ok(()), // Optimize whole Hugr but keep all functions
            Either::Right(PassScope::PreservePublic) => {
                for n in hugr.children(hugr.module_root()) {
                    if let Some(fd) = hugr.get_optype(n).as_func_defn()
                        && fd.visibility() == &Visibility::Public
                    {
                        entry_points.push(n);
                    }
                }
                if hugr.entrypoint() != hugr.module_root() {
                    entry_points.push(hugr.entrypoint());
                }
            }
            Either::Right(PassScope::PreserveEntrypoint) => {
                if hugr.entrypoint() == hugr.module_root() {
                    return Ok(());
                };
                entry_points.push(hugr.entrypoint())
            }
        }

        let mut reachable =
            reachable_funcs(&ModuleGraph::new(hugr), hugr, entry_points).collect::<HashSet<_>>();
        // Also prevent removing the entrypoint itself
        let mut n = Some(hugr.entrypoint());
        while let Some(n2) = n {
            n = hugr.get_parent(n2);
            if n == Some(hugr.module_root()) {
                reachable.insert(n2);
            }
        }

        let unreachable = hugr
            .children(hugr.module_root())
            .filter(|n| {
                OpTag::Function.is_superset(hugr.get_optype(*n).tag()) && !reachable.contains(n)
            })
            .collect::<Vec<_>>();
        for n in unreachable {
            hugr.remove_subtree(n);
        }
        Ok(())
    }
}

/// Deletes from the Hugr any functions that are not used by either `Call` or
/// `LoadFunction` nodes in reachable parts.
///
/// `entry_points` may provide a list of entry points, which must be [`FuncDefn`]s (children of the root).
/// The [HugrView::entrypoint] will also be used unless it is the [HugrView::module_root].
/// Note that for a [`Module`]-rooted Hugr with no `entry_points` provided, this will remove
/// all functions from the module.
///
/// # Errors
/// * If any node in `entry_points` is not a [`FuncDefn`]
///
/// [`FuncDefn`]: hugr_core::ops::OpType::FuncDefn
/// [`Module`]: hugr_core::ops::OpType::Module
#[deprecated(note = "Use remove_dead_funcs_scoped")]
#[expect(deprecated)]
pub fn remove_dead_funcs(
    h: &mut impl HugrMut<Node = Node>,
    entry_points: impl IntoIterator<Item = Node>,
) -> Result<(), ValidatePassError<Node, RemoveDeadFuncsError>> {
    validate_if_test(
        RemoveDeadFuncsPass::default().with_module_entry_points(entry_points),
        h,
    )
}

/// Deletes from the Hugr any functions that are not used by either [`Call`] or
/// [`LoadFunction`] nodes in reachable parts, according to the specified [PassScope].
///
/// [`Call`]: hugr_core::ops::OpType::Call
/// [`LoadFunction`]: hugr_core::ops::OpType::LoadFunction
// TODO: after removing the deprecated `remove_dead_funcs`, rename this over it
pub fn remove_dead_funcs_scoped<H: HugrMut<Node = Node>>(
    h: &mut H,
    scope: &PassScope,
) -> Result<(), ValidatePassError<Node, RemoveDeadFuncsError>> {
    validate_if_test(
        <RemoveDeadFuncsPass as ComposablePass<H>>::with_scope(
            RemoveDeadFuncsPass::default(),
            scope,
        ),
        h,
    )
}

#[cfg(test)]
mod test {
    use std::collections::HashMap;

    use hugr_core::ops::handle::NodeHandle;
    use hugr_core::{Hugr, Visibility};
    use itertools::Itertools;
    use rstest::rstest;

    use hugr_core::builder::{Dataflow, DataflowSubContainer, HugrBuilder, ModuleBuilder};
    use hugr_core::hugr::hugrmut::HugrMut;
    use hugr_core::{HugrView, extension::prelude::usize_t, types::Signature};

    use crate::PassScope;
    use crate::dead_funcs::remove_dead_funcs_scoped;

    fn hugr(use_entrypoint: bool) -> Hugr {
        let mut hb = ModuleBuilder::new();
        let o2 = hb
            .define_function("from_pub", Signature::new_endo(usize_t()))
            .unwrap();
        let o2inp = o2.input_wires();
        let o2 = o2.finish_with_outputs(o2inp).unwrap();
        let mut o1 = hb
            .define_function_vis(
                "pubfunc",
                Signature::new_endo(usize_t()),
                Visibility::Public,
            )
            .unwrap();

        let o1c = o1.call(o2.handle(), &[], o1.input_wires()).unwrap();
        o1.finish_with_outputs(o1c.outputs()).unwrap();

        let fm = hb
            .define_function("from_main", Signature::new_endo(usize_t()))
            .unwrap();
        let f_inp = fm.input_wires();
        let fm = fm.finish_with_outputs(f_inp).unwrap();
        let mut m = hb
            .define_function("main", Signature::new_endo(usize_t()))
            .unwrap();
        let m_in = m.input_wires();
        let mut dfb = m.dfg_builder(Signature::new_endo(usize_t()), m_in).unwrap();
        let c = dfb.call(fm.handle(), &[], dfb.input_wires()).unwrap();
        let dfg = dfb.finish_with_outputs(c.outputs()).unwrap();
        m.finish_with_outputs(dfg.outputs()).unwrap();
        let mut h = hb.finish_hugr().unwrap();
        if use_entrypoint {
            h.set_entrypoint(dfg.node());
        }
        h
    }

    #[rstest]
    #[case(false, [], vec![])] // No entry_points removes everything!
    #[case(true, [], vec!["from_main", "main"])]
    #[case(false, ["main"], vec!["from_main", "main"])]
    #[case(false, ["from_main"], vec!["from_main"])]
    #[case(false, ["pubfunc"], vec!["from_pub", "pubfunc"])]
    #[case(true, ["from_pub"], vec!["from_main", "from_pub", "main"])]
    #[case(false, ["from_pub", "pubfunc"], vec!["from_pub", "pubfunc"])]
    fn remove_dead_funcs_entry_points(
        #[case] use_hugr_entrypoint: bool,
        #[case] entry_points: impl IntoIterator<Item = &'static str>,
        #[case] retained_funcs: Vec<&'static str>,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut hugr = hugr(use_hugr_entrypoint);

        let avail_funcs = hugr
            .children(hugr.module_root())
            .filter_map(|n| {
                hugr.get_optype(n)
                    .as_func_defn()
                    .map(|fd| (fd.func_name().clone(), n))
            })
            .collect::<HashMap<_, _>>();

        #[expect(deprecated)]
        super::remove_dead_funcs(
            &mut hugr,
            entry_points
                .into_iter()
                .map(|name| *avail_funcs.get(name).unwrap())
                .collect::<Vec<_>>(),
        )
        .unwrap();

        let remaining_funcs = hugr
            .nodes()
            .filter_map(|n| {
                hugr.get_optype(n)
                    .as_func_defn()
                    .map(|fd| fd.func_name().as_str())
            })
            .sorted()
            .collect_vec();
        assert_eq!(remaining_funcs, retained_funcs);
        Ok(())
    }

    #[rstest]
    #[case(PassScope::PreserveAll, false, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(PassScope::EntrypointFlat, true, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(PassScope::EntrypointRecursive, false, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(PassScope::PreservePublic, true, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(PassScope::PreservePublic, false, vec!["from_pub", "pubfunc"])]
    #[case(PassScope::PreserveEntrypoint, true, vec!["from_main", "main"])]
    fn remove_dead_funcs_scope(
        #[case] scope: PassScope,
        #[case] use_entrypoint: bool,
        #[case] retained_funcs: Vec<&'static str>,
    ) {
        let mut hugr = hugr(use_entrypoint);
        remove_dead_funcs_scoped(&mut hugr, &scope).unwrap();

        let remaining_funcs = hugr
            .nodes()
            .filter_map(|n| {
                hugr.get_optype(n)
                    .as_func_defn()
                    .map(|fd| fd.func_name().as_str())
            })
            .sorted()
            .collect_vec();
        assert_eq!(remaining_funcs, retained_funcs);
    }
}
