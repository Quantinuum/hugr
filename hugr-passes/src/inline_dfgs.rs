//! Provides [`InlineDFGsPass`], a pass for inlining all DFGs in a Hugr.
use std::convert::Infallible;

use hugr_core::hugr::{
    hugrmut::HugrMut,
    patch::inline_dfg::{InlineDFG, InlineDFGError},
};
use itertools::Itertools;

use crate::{ComposablePass, PassScope};

/// Inlines all DFG nodes nested below the entrypoint.
///
/// See [InlineDFG] for a rewrite to inline single DFGs.
#[derive(Debug, Default, Clone)]
pub struct InlineDFGsPass {
    scope: PassScope,
}

impl<H: HugrMut> ComposablePass<H> for InlineDFGsPass {
    type Error = Infallible;
    type Result = ();

    fn run(&self, h: &mut H) -> Result<(), Self::Error> {
        let Some(r) = self.scope.root(h) else {
            return Ok(());
        };
        let dfgs = h
            .descendants(r)
            .filter(|&n| n != h.entrypoint() && h.get_optype(n).is_dfg())
            .collect_vec();
        for dfg in dfgs {
            h.apply_patch(InlineDFG(dfg.into()))
                .map_err(|err| -> Infallible {
                    match err {
                        InlineDFGError::CantInlineEntrypoint { .. } => {
                            unreachable!("We skipped the entrypoint")
                        }
                        InlineDFGError::NotDFG { .. } => unreachable!("Should be a DFG"),
                        _ => unreachable!("No other error cases"),
                    }
                })
                .unwrap();
        }
        Ok(())
    }

    fn with_scope(mut self, scope: &PassScope) -> Self {
        self.scope = scope.clone();
        self
    }
}

#[cfg(test)]
mod test {
    use hugr_core::{
        HugrView,
        builder::{DFGBuilder, Dataflow, DataflowHugr, DataflowSubContainer},
        extension::prelude::qb_t,
        types::Signature,
    };

    use crate::ComposablePass;

    use super::InlineDFGsPass;

    #[test]
    fn inline_dfgs() -> Result<(), Box<dyn std::error::Error>> {
        let mut outer = DFGBuilder::new(Signature::new_endo(vec![qb_t(), qb_t()]))?;
        let [a, b] = outer.input_wires_arr();

        let inner1 = outer.dfg_builder_endo([(qb_t(), a)])?;
        let [inner1_a] = inner1.input_wires_arr();
        let [a] = inner1.finish_with_outputs([inner1_a])?.outputs_arr();

        let mut inner2 = outer.dfg_builder_endo([(qb_t(), b)])?;
        let [inner2_b] = inner2.input_wires_arr();
        let inner2_inner = inner2.dfg_builder_endo([(qb_t(), inner2_b)])?;
        let [inner2_inner_b] = inner2_inner.input_wires_arr();
        let [inner2_b] = inner2_inner
            .finish_with_outputs([inner2_inner_b])?
            .outputs_arr();
        let [b] = inner2.finish_with_outputs([inner2_b])?.outputs_arr();

        let inner3 = outer.dfg_builder_endo([(qb_t(), a), (qb_t(), b)])?;
        let [inner3_a, inner3_b] = inner3.input_wires_arr();
        let [a, b] = inner3
            .finish_with_outputs([inner3_a, inner3_b])?
            .outputs_arr();

        let mut h = outer.finish_hugr_with_outputs([a, b])?;
        assert_eq!(h.num_nodes(), 5 * 3 + 4); // 5 DFGs with I/O + 4 nodes for module/func roots
        InlineDFGsPass::default().run(&mut h).unwrap();

        // Root should be the only remaining DFG
        assert!(h.get_optype(h.entrypoint()).is_dfg());
        assert!(
            h.entry_descendants()
                .skip(1)
                .all(|n| !h.get_optype(n).is_dfg())
        );
        assert_eq!(h.num_nodes(), 3 + 4); // 1 DFG with I/O + 4 nodes for module/func roots
        Ok(())
    }
}
