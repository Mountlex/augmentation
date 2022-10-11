use crate::{
    path::{proof::PathContext, CycleEdge, PseudoCycleInstance, SuperNode},
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

        let (cycle_idx, hit) = data
            .pseudo_cycle
            .nodes
            .iter()
            .enumerate()
            .max_by_key(|(_, n)| n.path_idx())
            .unwrap();

        // [hit,last,....,new_last]
        let extension = vec![
            data.pseudo_cycle.nodes.split_at(cycle_idx).1,
            data.pseudo_cycle.nodes.split_at(cycle_idx).0,
        ]
        .concat();

        let old_last_node = extension[1].get_zoomed();
        let old_last_comp = old_last_node.get_comp();
        let old_last_np = old_last_node.npc.is_nice_pair(
            old_last_node.in_node.unwrap(),
            old_last_node.out_node.unwrap(),
        );

        let new_last = extension.last().unwrap();
        let new_last_comp = new_last.get_comp();

        let new_prelast = &extension[extension.len() - 2];
        let new_prelast_comp = new_prelast.get_comp();

        if new_prelast_comp.is_c5() {
            if let SuperNode::Zoomed(prelast) = new_prelast {
                let valid_in_out =
                    prelast.valid_in_out(prelast.in_node.unwrap(), prelast.out_node.unwrap(), true);
                if !valid_in_out {
                    return ProofNode::new_leaf(
                        format!("New prelast is C5 but does not fulfill nice path properties",),
                        false,
                    );
                }
            } else {
                return ProofNode::new_leaf(
                    format!("New prelast is C5 but we cannot check nice path properties",),
                    false,
                );
            }
        }

        if (old_last_comp.is_c3() || old_last_comp.is_c4()) && !old_last_np {
            return ProofNode::new_leaf(
                format!(
                    "Cannot rearrange cycle: last comp is {} but has no nice pair!",
                    old_last_comp
                ),
                false,
            );
        }

        // Case 2
        // let mut part1 = data.pseudo_cycle.nodes.split_at(cycle_idx + 1).0.to_vec();
        // let mut part2 = data.pseudo_cycle.nodes.split_at(cycle_idx + 1).1.to_vec();
        // part1.reverse();
        // part2.reverse();
        // let path2 = vec![part1, part2].concat();

        if let SuperNode::Abstract(hit_node) = hit {
            let hit_comp = hit_node.get_comp();

            if hit_comp.is_c3() || hit_comp.is_c4() {
                // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
                return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has nice pair in cycle, so we cannot guarantee nice pair on path!", hit_comp), false);
            }
        } else if let SuperNode::Zoomed(cycle_hit_node) = hit {
            let hit_comp = cycle_hit_node.get_comp();
            if let SuperNode::Zoomed(path_hit_node) = &data.path_matching[hit.path_idx()] {
                if let CycleEdge::Fixed(cycle_edge) = data.cycle_edge {
                    let cycle_hit_endpoint = cycle_edge.endpoint_at(hit.path_idx()).unwrap();

                    let hit_np = path_hit_node.valid_out(cycle_hit_endpoint, false);

                    if (hit_comp.is_c3() || hit_comp.is_c4()) && !hit_np {
                        // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
                        return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has no nice pair in new instance!", old_last_comp), false);
                    }
                }
            }
        }

        // Complex > C5 > C4 > Large > C6 > C3

        // Reduce C3 to anything except C3
        if old_last_comp.is_c3() && !new_last_comp.is_c3() {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C6 to anything except C3 and C6
        if old_last_comp.is_c6() && !new_last_comp.is_c3() && !new_last_comp.is_c6() {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce Large to anything except C3 and C6 and Large
        if old_last_comp.is_large()
            && !new_last_comp.is_large()
            && !new_last_comp.is_c3()
            && !new_last_comp.is_c6()
        {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C4 to anything except Large, C6 or C3
        if old_last_comp.is_c4()
            && !new_last_comp.is_large()
            && !new_last_comp.is_c6()
            && !new_last_comp.is_c3()
            && !new_last_comp.is_c4()
        {
            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce anything that is not complex to complex
        if !old_last_comp.is_complex() && new_last_comp.is_complex() {
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
