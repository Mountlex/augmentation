use itertools::Itertools;

use crate::{
    comps::Component,
    path::{
        enumerators::{matching_nodes::MatchingNodesEnumeratorOutput, nice_pairs::NPCEnumOutput},
        proof::{ProofContext, Tactic},
        utils::hamiltonian_paths,
        NicePairConfig, ThreeMatching,
    },
    proof_tree::ProofNode,
    types::Edge,
};

impl From<NPCEnumOutput<MatchingNodesEnumeratorOutput>> for LongerNicePathViaMatchingSwapInput {
    fn from(o: NPCEnumOutput<MatchingNodesEnumeratorOutput>) -> Self {
        LongerNicePathViaMatchingSwapInput {
            m_last: o.input.three_matching,
            prelast: o.input.left_comp,
            last: o.input.last_comp,
            prelast_matched: o.input.left_matched,
            last_matched: o.input.right_matched,
            np_config_prelast: o.npc,
            np_config_last: o.input.npc_last,
        }
    }
}

pub struct LongerNicePathViaMatchingSwapInput {
    m_last: ThreeMatching,
    prelast: Component,
    last: Component,
    prelast_matched: Vec<u32>,
    last_matched: Vec<u32>,
    np_config_prelast: NicePairConfig,
    np_config_last: NicePairConfig,
}

pub struct LongerNicePathViaMatchingSwap;

impl Tactic for LongerNicePathViaMatchingSwap {
    type In = LongerNicePathViaMatchingSwapInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        if data.last_matched.len() == 2
            && (data.m_last.1.hits_outside() || data.m_last.2.hits_outside())
            && (data.m_last.1.hits_path() == Some(context.path_len - 2)
                || data.m_last.2.hits_path() == Some(context.path_len - 2))
        {
            let m_outside = vec![data.m_last.1, data.m_last.2]
                .into_iter()
                .find(|&m| m.hits_outside())
                .unwrap();
            let (m_path, m_other) = if data.last_matched[0] == data.m_last.0.source() {
                (
                    Edge(data.prelast_matched[0], data.last_matched[0]),
                    Edge(data.prelast_matched[1], data.last_matched[1]),
                )
            } else {
                (
                    Edge(data.prelast_matched[1], data.last_matched[1]),
                    Edge(data.prelast_matched[0], data.last_matched[0]),
                )
            };

            // If matching edge swap cannot be a nice path
            if (data.last.is_c3()
                || data.last.is_c4()
                || data.last.is_c5()
                || data.last.is_complex())
                && !data
                    .np_config_last
                    .is_nice_pair(m_other.1, m_outside.source())
            {
                return ProofNode::new_leaf(
                    "No longer path via swapping matching edges: no nice pairs".into(),
                    false,
                );
            }

            // Now if C_l-1 does not care about nice pairs, we are done!
            if data.prelast.is_c6() || data.prelast.is_large() {
                return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true);
            }

            // For others, we have to check that swaping the path edges keeps a nice pair
            if data
                .prelast
                .graph()
                .nodes()
                .filter(|left_in| *left_in != m_path.0)
                .all(|left_in| {
                    // for any left_in, we consider all possible hamiltonian paths for the current nice pair
                    hamiltonian_paths(left_in, m_path.0, &data.prelast.nodes())
                        .into_iter()
                        .all(|ham_path| {
                            let edges = ham_path
                                .windows(2)
                                .map(|e| (e[0], e[1]))
                                .chain(data.prelast.edges().into_iter())
                                .collect_vec();

                            // If for every such path, a nice pair using _any_ hamiltonian path for left_in and the new path edge endpoint is possible, it must be a nice pair
                            hamiltonian_paths(left_in, m_other.0, &data.prelast.nodes())
                                .into_iter()
                                .any(|path| {
                                    path.windows(2).map(|e| (e[0], e[1])).all(|(u, v)| {
                                        edges.contains(&(u, v)) || edges.contains(&(v, u))
                                    })
                                })
                        })
                })
            {
                return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true);
            }
            return ProofNode::new_leaf(
                "No longer path via swapping matching edges: no swapping".into(),
                false,
            );
        } else {
            return ProofNode::new_leaf(
                "No longer path via swapping matching edges: no preconditions".into(),
                false,
            );
        }
    }
}
