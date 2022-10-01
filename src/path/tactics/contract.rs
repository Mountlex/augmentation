use itertools::Itertools;

use crate::{
    path::{proof::PathContext, utils::hamiltonian_paths, AugmentedPathInstance},
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
};
#[derive(Clone)]
pub struct ContractabilityTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl ContractabilityTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for ContractabilityTactic {
    fn print_stats(&self) {
        println!(
            "Contractability proof {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}

impl Tactic<AugmentedPathInstance, PathContext> for ContractabilityTactic {
    fn action(
        &mut self,
        data: &AugmentedPathInstance,
        context: &PathContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let last = data.path.nodes.last().unwrap().get_zoomed();
        let last_comp = last.get_comp();

        if last_comp.is_complex() || last_comp.is_large() || last_comp.is_c3() {
            return ProofNode::new_leaf(
                "Contractability check not applied: component is C3, Large or Complex".into(),
                false,
            );
        }

        let free_nodes = data.nodes_without_edges(context.path_len - 1);
        let used_nodes = data.nodes_with_edges(context.path_len - 1);

        let num_edges_between_free_nodes = last_comp
            .graph()
            .all_edges()
            .filter(|(u, v, _)| free_nodes.contains(u) && free_nodes.contains(v))
            .count();

        let opt_lb = free_nodes.len() * 2 - num_edges_between_free_nodes;

        if opt_lb * 5 >= last_comp.graph().node_count() * 4 {
            let chord_implies_absent_np = free_nodes.iter().combinations(2).any(|free_edge| {
                used_nodes
                    .iter()
                    .combinations(2)
                    .filter(|m| !last.npc.is_nice_pair(*m[0], *m[1]))
                    .any(|m| {
                        hamiltonian_paths(*m[0], *m[1], last_comp.nodes())
                            .iter()
                            .any(|path| {
                                path.windows(2).all(|e| {
                                    last_comp.is_adjacent(&e[0], &e[1])
                                        || (*free_edge[0] == e[0] && *free_edge[1] == e[1])
                                        || (*free_edge[1] == e[0] && *free_edge[0] == e[1])
                                })
                            })
                    })
            });

            if chord_implies_absent_np {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!(
                        "Component {} is contractable and chords imply absent nice pairs!",
                        last_comp
                    ),
                    true,
                );
            } else {
                return ProofNode::new_leaf(
                    format!("Component {} is contractable, but there might be inner chords which don't contradict nice pairs!", last_comp),
                    false,
                );
            }
        } else {
            return ProofNode::new_leaf(
                format!("Component {} is not contractable!", last_comp),
                false,
            );
        }
    }
}
