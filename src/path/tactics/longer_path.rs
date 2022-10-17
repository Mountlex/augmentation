use crate::{
    path::{
        proof::PathContext, AugmentedPathInstance, PathRearrangementInstance, Pidx,
        SelectedHitInstance, SuperNode,
    },
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
};

use super::cycle_rearrange::check_fixed_extension_feasible;

#[derive(Clone)]
pub struct LongerPathTactic {
    num_calls: usize,
    num_proofs: usize,
    finite_path: bool
}

impl LongerPathTactic {
    pub fn new(finite_path: bool) -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
            finite_path
        }
    }
}

impl Statistics for LongerPathTactic {
    fn print_stats(&self) {
        println!("Longer path {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<PathRearrangementInstance, PathContext> for LongerPathTactic {
    fn precondition(&self, data: &PathRearrangementInstance, _context: &PathContext) -> bool {
        !data
            .instance
            .outside_hits_from(data.extension.last().unwrap().path_idx())
            .is_empty()
    }

    fn action(&mut self, data: &PathRearrangementInstance, _context: &PathContext) -> ProofNode {
        let new_last = data.extension.last().unwrap();
        let outside_hits = data.instance.outside_hits_from(new_last.path_idx());
        for outside_hit in outside_hits {
            if new_last.get_zoomed().valid_out(outside_hit.source(), true) {
                let mut feasible =
                    check_fixed_extension_feasible(&data.extension, &data.instance, false);
                feasible.eval();
                if feasible.success() {
                    self.num_proofs += 1;
                    return ProofNode::new_leaf(
                        format!("Longer nice path found via edge ({})!", outside_hit),
                        true,
                    );
                }
            }
        }
        return ProofNode::new_leaf(
            format!("No outside matching hit does is a valid out edge for the last node!"),
            false,
        );
    }
}

impl Tactic<SelectedHitInstance, PathContext> for LongerPathTactic {
    fn precondition(&self, data: &SelectedHitInstance, context: &PathContext) -> bool {
        Tactic::<AugmentedPathInstance, PathContext>::precondition(self, &data.instance, context)
    }

    fn action(&mut self, data: &SelectedHitInstance, context: &PathContext) -> ProofNode {
        Tactic::<AugmentedPathInstance, PathContext>::action(self, &data.instance, context)
    }
}

impl Tactic<AugmentedPathInstance, PathContext> for LongerPathTactic {
    fn action(
        &mut self,
        data: &AugmentedPathInstance,
        _context: &PathContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let outside_hits = data.outside_hits_from(Pidx::Last);

        for outside_hit in outside_hits {
            //   0 --- 1 --- 2 ---
            //   |
            //  out
            if data[Pidx::Last]
                .get_zoomed()
                .valid_out(outside_hit.source, true)
            {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!("Longer nice path found via edge ({})!", outside_hit),
                    true,
                );
            }

            for prelast_edge in data.fixed_edges_between(Pidx::Last, Pidx::Prelast) {
                let prelast_cond = if let SuperNode::Zoomed(prelast) = &data[Pidx::Prelast] {
                    prelast.valid_out(prelast_edge.endpoint_at(Pidx::Prelast).unwrap(), false)
                } else {
                    true
                };

                if prelast_cond
                    && data[Pidx::Last].get_zoomed().valid_in_out(
                        prelast_edge.endpoint_at(Pidx::Last).unwrap(),
                        outside_hit.source,
                        true,
                    )
                {
                    self.num_proofs += 1;
                    return ProofNode::new_leaf(
                        format!("Longer nice path found via edge ({})!", outside_hit),
                        true,
                    );
                }
            }
        }

        if self.finite_path {
            let start_idx = Pidx::from(data.path_len() - 1);
            let outside_hits = data.outside_hits_from(start_idx);

            for outside_hit in outside_hits {
                //   0 --- 1 --- 2
                //               |
                //               out
                if data[start_idx.succ().unwrap()]
                    .get_zoomed()
                    .valid_out(outside_hit.source, true)
                {
                    self.num_proofs += 1;
                    return ProofNode::new_leaf(
                        format!("Longer nice path found via edge ({})!", outside_hit),
                        true,
                    );
                }
    
                for prelast_edge in data.fixed_edges_between(start_idx, start_idx.succ().unwrap()) {
                    let prelast_cond = if let SuperNode::Zoomed(prelast) = &data[start_idx.succ().unwrap()] {
                        prelast.valid_in(prelast_edge.endpoint_at(start_idx.succ().unwrap()).unwrap(), false)
                    } else {
                        true
                    };
    
                    if prelast_cond
                        && data[start_idx].get_zoomed().valid_in_out(
                            outside_hit.source,
                            prelast_edge.endpoint_at(start_idx).unwrap(),
                            true,
                        )
                    {
                        self.num_proofs += 1;
                        return ProofNode::new_leaf(
                            format!("Longer nice path found via edge ({})!", outside_hit),
                            true,
                        );
                    }
                }
            }
        }

        ProofNode::new_leaf(format!("No longer nice path possible!"), false)
    }

    fn precondition(&self, data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        !(data.outside_edges_on(Pidx::Last).is_empty() && data.outside_edges_on(Pidx::from(data.path_len() - 1)).is_empty() )
    }
}
