use crate::{
    path::{proof::PathContext, AugmentedPathInstance, Pidx, SelectedHitInstance, SuperNode},
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
};

#[derive(Clone)]
pub struct LongerPathTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl LongerPathTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for LongerPathTactic {
    fn print_stats(&self) {
        println!("Longer path {} / {}", self.num_proofs, self.num_calls);
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

        let outside_hits = data.all_outside_hits();

        for outside_hit in outside_hits {
            if outside_hit.source_path().is_last() {
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
            } else if outside_hit.source_path().is_prelast() {
                //   -------------  <-- cycle_edge
                //   |           |
                //   0 --- 1 --- 2 ---
                //         |
                //        out
                for cycle_edge in data.fixed_edges_between(Pidx::Last, Pidx::N(2)) {
                    for prelast_edge in data.fixed_edges_between(Pidx::Prelast, Pidx::Last) {
                        if data[Pidx::N(2)]
                            .get_zoomed()
                            .valid_out(cycle_edge.endpoint_at(Pidx::N(2)).unwrap(), false)
                            && data[Pidx::Last].get_zoomed().valid_in_out(
                                cycle_edge.endpoint_at(Pidx::Last).unwrap(),
                                prelast_edge.endpoint_at(Pidx::Last).unwrap(),
                                false,
                            )
                            && data[Pidx::Prelast].get_zoomed().valid_in_out(
                                prelast_edge.endpoint_at(Pidx::Prelast).unwrap(),
                                outside_hit.source(),
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
        }
        ProofNode::new_leaf(format!("No longer nice path possible!"), false)
    }

    fn precondition(&self, data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        !data.all_outside_hits().is_empty()
    }
}
