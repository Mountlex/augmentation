use crate::{
    path::{proof::PathContext, AugmentedPathInstance, SelectedHitInstance, SuperNode},
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
        context: &PathContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let outside_hits = data.all_outside_hits();

        for outside_hit in outside_hits {
            let source_path_idx = outside_hit.source_path();
            let source_path_node = &data.path[outside_hit.source_path()];

            if outside_hit.source_path() == context.path_len - 1 {
                if source_path_node
                    .get_zoomed()
                    .valid_out(outside_hit.source, true)
                {
                    self.num_proofs += 1;
                    return ProofNode::new_leaf(
                        format!("Longer nice path found via edge ({})!", outside_hit),
                        true,
                    );
                }

                for prelast_edge in
                    data.fixed_edges_between(context.path_len - 2, context.path_len - 1)
                {
                    let prelast_cond =
                        if let SuperNode::Zoomed(prelast) = &data.path[context.path_len - 2] {
                            prelast.valid_out(
                                prelast_edge.endpoint_at(context.path_len - 2).unwrap(),
                                false,
                            )
                        } else {
                            true
                        };

                    if prelast_cond
                        && source_path_node.get_zoomed().valid_in_out(
                            prelast_edge.endpoint_at(source_path_idx).unwrap(),
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
            } else if outside_hit.source_path() == context.path_len - 2 {
                for cycle_edge in data.fixed_edges_between(1, 3) {
                    for prelast_edge in
                        data.fixed_edges_between(context.path_len - 2, context.path_len - 1)
                    {
                        if data.path[1]
                            .get_zoomed()
                            .valid_out(cycle_edge.endpoint_at(1).unwrap(), false)
                            && data.path[3].get_zoomed().valid_in_out(
                                cycle_edge.endpoint_at(3).unwrap(),
                                prelast_edge.endpoint_at(3).unwrap(),
                                false,
                            )
                            && data.path[2].get_zoomed().valid_in_out(
                                prelast_edge.endpoint_at(2).unwrap(),
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
