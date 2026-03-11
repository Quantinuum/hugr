//! Pass for removing statically-unreachable functions from a Hugr

use std::collections::HashSet;

use hugr_core::{
    HugrView, Node, Visibility,
    hugr::hugrmut::HugrMut,
    module_graph::{ModuleGraph, StaticNode},
    ops::{OpTag, OpTrait},
};
use petgraph::visit::{Dfs, Walker};

use crate::composable::{Preserve, WithScope};
use crate::{ComposablePass, PassScope};

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

#[derive(Debug, Clone, Default)]
/// A configuration for the Dead Function Removal pass.
pub struct RemoveDeadFuncsPass {
    entry_points: PassScope,
}

impl<H: HugrMut> ComposablePass<H> for RemoveDeadFuncsPass {
    type Error = RemoveDeadFuncsError;
    type Result = ();

    fn run(&self, hugr: &mut H) -> Result<(), RemoveDeadFuncsError> {
        let mut entry_points = Vec::new();
        match &self.entry_points {
            // If the entrypoint is the module root, not allowed to touch anything.
            // Otherwise, we must keep the entrypoint (and can touch only inside it).
            PassScope::EntrypointFlat | PassScope::EntrypointRecursive
            // Optimize whole Hugr but keep all functions
            | PassScope::Global(Preserve::All) => return Ok(()),
            PassScope::Global(Preserve::Entrypoint) if hugr.entrypoint() != hugr.module_root() => {
                entry_points.push(hugr.entrypoint());
            }
            PassScope::Global(_) => {
                for n in hugr.children(hugr.module_root()) {
                    if hugr.get_optype(n).as_func_defn().is_some_and(|fd| fd.visibility() == &Visibility::Public)
                    {
                        entry_points.push(n);
                    }
                }
                if hugr.entrypoint() != hugr.module_root() {
                    entry_points.push(hugr.entrypoint());
                }
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

impl WithScope for RemoveDeadFuncsPass {
    fn with_scope(mut self, scope: impl Into<PassScope>) -> Self {
        self.entry_points = scope.into();
        self
    }
}

#[cfg(test)]
mod test {

    use hugr_core::builder::{Dataflow, DataflowSubContainer, HugrBuilder, ModuleBuilder};
    use hugr_core::hugr::hugrmut::HugrMut;
    use hugr_core::ops::handle::NodeHandle;
    use hugr_core::{Hugr, Visibility};
    use hugr_core::{HugrView, extension::prelude::usize_t, types::Signature};
    use itertools::Itertools;
    use rstest::rstest;

    use super::RemoveDeadFuncsPass;
    use crate::PassScope;
    use crate::composable::{Preserve, WithScope, test::run_validating};

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
    #[case(Preserve::All, false, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(PassScope::EntrypointFlat, true, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(PassScope::EntrypointRecursive, false, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(Preserve::Public, true, vec!["from_main", "from_pub", "main", "pubfunc"])]
    #[case(Preserve::Public, false, vec!["from_pub", "pubfunc"])]
    #[case(Preserve::Entrypoint, true, vec!["from_main", "main"])]
    fn remove_dead_funcs_scope(
        #[case] scope: impl Into<PassScope>,
        #[case] use_entrypoint: bool,
        #[case] retained_funcs: Vec<&'static str>,
    ) {
        let scope = scope.into();
        let mut hugr = hugr(use_entrypoint);
        run_validating(RemoveDeadFuncsPass::default().with_scope(scope), &mut hugr).unwrap();

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
