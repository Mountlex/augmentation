use itertools::Itertools;

use crate::{
    comps::Component,
    path::{proof::PathContext, utils::hamiltonian_paths, AugmentedPathInstance, Pidx, ZoomedNode},
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
};
#[derive(Clone)]
pub struct ContractabilityTactic {
    num_calls: usize,
    num_proofs: usize,
    finite: bool,
}

impl ContractabilityTactic {
    pub fn new(finite: bool) -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
            finite,
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
        _context: &PathContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        
        if self.finite {
            for node in &data.nodes {
                if node.is_zoomed() {
                    let res = check_for_comp(data, node.get_comp(), node.get_zoomed(), node.path_idx());
                        if res.success() {
                            self.num_proofs += 1;
                            return res
                        }
                }
            }
            return ProofNode::new_leaf(format!("No contractable components"), false)
        } else {
            let last = &data[Pidx::Last];
            return check_for_comp(data, last.get_comp(), last.get_zoomed(), last.path_idx())
        }

    }
}

pub fn check_for_comp(data: &AugmentedPathInstance, comp: &Component, node: &ZoomedNode, idx: Pidx) -> ProofNode {
    if comp.is_complex() || comp.is_large() || comp.is_c3() || comp.is_c4() {
        return ProofNode::new_leaf(
            "Contractability check not applied: component is C3, Large or Complex".into(),
            false,
        )
        .into();
    }

    let free_nodes = data.nodes_without_edges(idx);
    let used_nodes = data.nodes_with_edges(idx);

    let num_edges_between_free_nodes = comp
        .graph()
        .all_edges()
        .filter(|(u, v, _)| free_nodes.contains(u) && free_nodes.contains(v))
        .count();

    let opt_lb = free_nodes.len() * 2 - num_edges_between_free_nodes;

    if opt_lb * 5 >= comp.graph().node_count() * 4 {
        let chord_implies_absent_np = free_nodes.iter().combinations(2).any(|free_edge| {
            used_nodes
                .iter()
                .combinations(2)
                .filter(|m| !node.npc.is_nice_pair(*m[0], *m[1]))
                .any(|m| {
                    hamiltonian_paths(*m[0], *m[1], comp.nodes())
                        .iter()
                        .any(|path| {
                            path.windows(2).all(|e| {
                                comp.is_adjacent(&e[0], &e[1])
                                    || (*free_edge[0] == e[0] && *free_edge[1] == e[1])
                                    || (*free_edge[1] == e[0] && *free_edge[0] == e[1])
                            })
                        })
                })
        });

        if chord_implies_absent_np {
            return ProofNode::new_leaf(
                format!(
                    "Component {} is contractable and chords imply absent nice pairs!",
                    comp
                ),
                true,
            )
            .into();
        } else {
            return ProofNode::new_leaf(
                    format!("Component {} is contractable, but there might be inner chords which don't contradict nice pairs!", comp),
                    false,
                ).into();
        }
    } else {
        return ProofNode::new_leaf(format!("Component {} is not contractable!", comp), false)
            .into();
    }
}
