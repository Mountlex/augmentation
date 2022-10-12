use crate::{
    comps::Component,
    path::{proof::PathContext, AugmentedPathInstance, CycleEdge, PseudoCycleInstance, SuperNode},
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

        let (cycle_idx, _) = data
            .pseudo_cycle
            .nodes
            .iter()
            .enumerate()
            .max_by_key(|(_, n)| n.path_idx())
            .unwrap();

        // [hit,<cycle_idx + 1>....,new_last]
        let path1 = vec![
            data.pseudo_cycle.nodes.split_at(cycle_idx).1,
            data.pseudo_cycle.nodes.split_at(cycle_idx).0,
        ]
        .concat();

        // [hit,<cycle_idx - 1>....,new_last]
        let mut p1 = data.pseudo_cycle.nodes.split_at(cycle_idx + 1).0.to_vec();
        let mut p2 = data.pseudo_cycle.nodes.split_at(cycle_idx + 1).1.to_vec();
        p1.reverse();
        p2.reverse();
        let path2 = vec![p1, p2].concat();

        let mut res = check_feasible_path(path1, &data.cycle_edge, &data.path_matching);
        if res.eval().success() {
            res
        } else {
            check_feasible_path(path2, &data.cycle_edge, &data.path_matching)
        }
    }

    fn precondition(&self, data: &PseudoCycleInstance, _context: &PathContext) -> bool {
        data.pseudo_cycle.consecutive_end()
    }
}

fn check_feasible_path(
    extension: Vec<SuperNode>,
    cycle_edge: &CycleEdge,
    instance: &AugmentedPathInstance,
) -> ProofNode {
    let old_last_node = extension
        .iter()
        .find(|n| n.path_idx().is_last())
        .unwrap()
        .get_zoomed();
    let old_last_comp = old_last_node.get_comp();

    let new_last = extension.last().unwrap();
    let new_last_comp = new_last.get_comp();
    let hit = extension.first().unwrap();

    if matches!(cycle_edge, CycleEdge::Fixed) {
        for i in 1..extension.len() - 1 {
            let node = &extension[i];
            if let SuperNode::Zoomed(node) = node {
                let valid_in_out = node.valid_in_out(
                    node.in_node.unwrap(),
                    node.out_node.unwrap(),
                    i == extension.len() - 2,
                );
                if !valid_in_out {
                    return ProofNode::new_leaf(
                        format!("New path does not fulfill nice path properties!"),
                        false,
                    );
                }
            } else {
                panic!()
            }
        }

        if let SuperNode::Zoomed(hit_node) = hit {
            if let SuperNode::Zoomed(path_hit_node) = &instance[hit.path_idx()] {
                let path_hit_in = path_hit_node.in_node.unwrap();
                if !hit_node.valid_in(path_hit_in, false) {
                    // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
                    return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has no nice pair in new instance!", hit_node.get_comp()), false);
                }
            }
        } else {
            panic!()
        }
    } else {
        let new_prelast = &extension[extension.len() - 2];
        let new_prelast_comp = new_prelast.get_comp();

        if new_prelast_comp.is_c5() {
            return ProofNode::new_leaf(
                format!("New prelast is C5 but we cannot check nice path properties",),
                false,
            );
        }
        let old_last_np = old_last_node.npc.is_nice_pair(
            old_last_node.in_node.unwrap(),
            old_last_node.out_node.unwrap(),
        );

        if (old_last_comp.is_c3() || old_last_comp.is_c4()) && !old_last_np {
            return ProofNode::new_leaf(
                format!(
                    "Cannot rearrange cycle: last comp is {} but has no nice pair!",
                    old_last_comp
                ),
                false,
            );
        }

        if let SuperNode::Abstract(hit_node) = hit {
            let hit_comp = hit_node.get_comp();

            if hit_comp.is_c3() || hit_comp.is_c4() {
                // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
                return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has nice pair in cycle, so we cannot guarantee nice pair on path!", hit_comp), false);
            }
        } else {
            panic!()
        }
    }

    feasible_reduction(&old_last_comp, &new_last_comp)
}

fn feasible_reduction(old_last_comp: &Component, new_last_comp: &Component) -> ProofNode {
    // Complex > C5 > C4 > Large > C6 > C3

    // Reduce C3 to anything except C3
    if old_last_comp.is_c3() && !new_last_comp.is_c3() {
        return ProofNode::new_leaf(
            format!("Rearrange cycle: now ends with {}!", new_last_comp),
            true,
        );
    }

    // Reduce C6 to anything except C3 and C6
    if old_last_comp.is_c6() && !new_last_comp.is_c3() && !new_last_comp.is_c6() {
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
        return ProofNode::new_leaf(
            format!("Rearrange cycle: now ends with {}!", new_last_comp),
            true,
        );
    }

    // Reduce anything that is not complex to complex
    if !old_last_comp.is_complex() && new_last_comp.is_complex() {
        return ProofNode::new_leaf(
            format!("Rearrange cycle: now ends with {}!", new_last_comp),
            true,
        );
    }

    return ProofNode::new_leaf(format!("No feasible reduction"), false);
}
