use itertools::Itertools;

use crate::{
    comps::{Component, Node},
    path::{proof::Tactic, utils::hamiltonian_paths, NicePairConfig, enumerators::{nice_pairs::NPCEnumOutput, matching_hits::MatchingHitEnumeratorOutput}},
    proof_tree::ProofNode,
};

impl From<NPCEnumOutput<MatchingHitEnumeratorOutput>> for ContractabilityInput {
    fn from(o: NPCEnumOutput<MatchingHitEnumeratorOutput>) -> Self {
        ContractabilityInput {
            comp: o.input.nice_path.last_comp().clone(),
            matching_nodes: o.input.three_matching.sources(),
            npc: o.npc
        }
    }
}


pub struct ContractabilityInput {
    pub comp: Component,
    pub matching_nodes: Vec<Node>,
    pub npc: NicePairConfig,
}

pub struct ContractabilityTactic;

impl Tactic for ContractabilityTactic {
    type In = ContractabilityInput;

    fn action(
        &self,
        data: Self::In,
        context: &crate::path::proof::ProofContext,
    ) -> crate::proof_tree::ProofNode {
        if data.comp.is_complex() || data.comp.is_large() || data.comp.is_c6() {
            return ProofNode::new_leaf(
                "Contractability check not applied: component is C6, Large or Complex".into(),
                false,
            );
        }

        let free_nodes = data
            .comp
            .graph()
            .nodes()
            .filter(|n| !data.matching_nodes.contains(n))
            .collect_vec();

        let num_edges_between_free_nodes = data
            .comp
            .graph()
            .all_edges()
            .filter(|(u, v, _)| free_nodes.contains(u) && free_nodes.contains(v))
            .count();

        let opt_lb = free_nodes.len() * 2 - num_edges_between_free_nodes;

        if opt_lb * 5 >= data.comp.graph().node_count() * 4 {
            let chord_implies_absent_np = free_nodes.iter().combinations(2).any(|free_edge| {
                data.matching_nodes
                    .iter()
                    .combinations(2)
                    .filter(|m| !data.npc.is_nice_pair(*m[0], *m[1]))
                    .any(|m| {
                        hamiltonian_paths(*m[0], *m[1], &data.comp.nodes())
                            .iter()
                            .any(|path| {
                                path.windows(2).all(|e| {
                                    data.comp.is_adjacent(e[0], e[1]) || 
                                    (*free_edge[0] == e[0] && *free_edge[1] == e[1])
                                        || (*free_edge[1] == e[0] && *free_edge[0] == e[1])
                                })
                            })
                    })
            });

            if chord_implies_absent_np {
                return ProofNode::new_leaf(format!("Component {} is contractable and chords imply absent nice pairs!", data.comp), true)
            } else {
                return ProofNode::new_leaf(
                    format!("Component {} is contractable, but there might be inner chords which don't contradict nice pairs!", data.comp),
                    false,
                );
            }
        } else {
            return ProofNode::new_leaf(
                format!("Component {} is not contractable!", data.comp),
                false,
            );
        }

        
    }
}
