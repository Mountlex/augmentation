use crate::{
    path::{proof::PathContext, PseudoCycleInstance, SuperNode, CycleEdge},
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
};

#[derive(Clone)]
pub struct CycleRearrangeTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl CycleRearrangeTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for CycleRearrangeTactic {
    fn print_stats(&self) {
        println!("Cycle rearrange {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<PseudoCycleInstance, PathContext> for CycleRearrangeTactic {
    fn action(&mut self, data: &PseudoCycleInstance, _context: &PathContext) -> ProofNode {
        self.num_calls += 1;

        let last_node = data.pseudo_cycle.nodes.first().unwrap().get_zoomed();
        let last_comp = last_node.get_comp();
        let last_np = last_node
            .npc
            .is_nice_pair(last_node.in_node.unwrap(), last_node.out_node.unwrap());

        let new_last = &data.pseudo_cycle.nodes[data.pseudo_cycle.nodes.len() - 2];
        let new_last_comp = new_last.get_comp();

        if let SuperNode::Abstract(hit_node) = data.pseudo_cycle.nodes.last().unwrap() {
            let hit_comp = hit_node.get_comp();
            let hit_np = hit_node.nice_pair;

            if (last_comp.is_c3() || last_comp.is_c4()) && !last_np {
                return ProofNode::new_leaf(
                    format!(
                        "Cannot rearrange cycle: last comp is {} but has no nice pair!",
                        last_comp
                    ),
                    false,
                );
            }

            if (hit_comp.is_c3() || hit_comp.is_c4()) && !hit_np {
                // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
                return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has nice pair in cycle, so we cannot guarantee nice pair on path!", hit_comp), false);
            }
        } else if let SuperNode::Zoomed(cycle_hit_node) = data.pseudo_cycle.nodes.last().unwrap() {
            let hit_comp = cycle_hit_node.get_comp();
            if let SuperNode::Zoomed(path_hit_node) = &data.path_matching[data.path_hit_idx] {
                if let CycleEdge::Fixed(cycle_edge) = data.cycle_edge {

                    let cycle_hit_endpoint = cycle_edge.endpoint_at(data.path_hit_idx).unwrap();

                    let hit_np = path_hit_node.valid_out(cycle_hit_endpoint, false);

                    if (hit_comp.is_c3() || hit_comp.is_c4()) && !hit_np {
                        // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
                        return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has no nice pair in new instance!", last_comp), false);
                    }
                }
            }
        }


        // Reduce C6 to anything except C3 and C6
        if last_comp.is_c6() && !new_last_comp.is_c3() && !new_last_comp.is_c6() {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C3 to anything except C3
        if last_comp.is_c3() && !new_last_comp.is_c3() {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C4 to C5
        if last_comp.is_c4() && new_last_comp.is_c5() {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce anything that is not complex to complex
        if !last_comp.is_complex() && new_last_comp.is_complex() {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        return ProofNode::new_leaf(format!("Cannot rearrange cycle"), false);
    }

    fn precondition(&self, data: &PseudoCycleInstance, _context: &PathContext) -> bool {
        match data.cycle_edge {
            crate::path::CycleEdge::Fixed(e) => e.path_incident(crate::path::Pidx::Last),
            crate::path::CycleEdge::Matching(e) => e.source_path().is_last(),
        }
    }
}
