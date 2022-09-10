use itertools::Itertools;
use petgraph::{algo::connected_components, visit::EdgeFiltered};

use crate::{
    bridges::{is_complex, ComplexCheckResult},
    comps::{edges_of_type, Component, CreditInvariant, EdgeType, Node},
    enumerators::{
        ComponentHitOutput, MatchingHitEnumeratorOutput, MatchingNodesEnumeratorOutput,
        NPCEnumOutput,
    },
    local_merge::prove_via_direct_merge,
    nice_path::{
        get_local_merge_graph, or, Edge, NicePairConfig, NicePath, PathMatchingEdge, ProofContext,
        Tactic, ThreeMatching, hamiltonian_paths, PathMatchingHits, MergeCases, SuperNode, ZoomedNode, check_nice_path_with_cycle,
    },
    proof_tree::ProofNode,
    Credit,
};

impl From<NPCEnumOutput<MatchingHitEnumeratorOutput>> for LongerPathInput {
    fn from(o: NPCEnumOutput<MatchingHitEnumeratorOutput>) -> Self {
        LongerPathInput {
            nice_path: o.input.nice_path,
            three_matching: o.input.three_matching,
            npc: o.npc,
        }
    }
}

pub struct LongerPathInput {
    nice_path: NicePath,
    three_matching: ThreeMatching,
    npc: NicePairConfig,
}

pub struct LongerPathTactic;

impl Tactic for LongerPathTactic {
    type In = LongerPathInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> crate::proof_tree::ProofNode {
        let check_input = LongerNicePathCheckInput {
            last_comp_ref: data.nice_path.nodes.last().unwrap().get_comp(),
            np_config: &data.npc,
            last_pseudo_edge: &data.three_matching.0,
        };

        if data.three_matching.1.hits_outside() && data.three_matching.2.hits_outside() {
            or(
                LongerNicePathCheck::check_for(&data.three_matching.1),
                LongerNicePathCheck::check_for(&data.three_matching.2),
            )
            .action(check_input, context)
        } else if data.three_matching.1.hits_outside() {
            LongerNicePathCheck::check_for(&data.three_matching.1).action(check_input, context)
        } else if data.three_matching.2.hits_outside() {
            LongerNicePathCheck::check_for(&data.three_matching.2).action(check_input, context)
        } else {
            ProofNode::new_leaf(format!("None of the matching edges hits outside"), false)
        }
    }
}

impl From<ComponentHitOutput> for LocalComplexMergeInput {
    fn from(o: ComponentHitOutput) -> Self {
        LocalComplexMergeInput {
            path: o.path,
            npc_last: o.npc_last,
            hit_comp_idx: o.hit_comp_idx,
            right_matched: o.right_matched,
        }
    }
}

pub struct LocalComplexMergeInput {
    pub path: NicePath,
    pub npc_last: NicePairConfig,
    pub hit_comp_idx: usize,
    pub right_matched: Vec<Node>,
}

pub struct LocalComplexMerge;

impl Tactic for LocalComplexMerge {
    type In = LocalComplexMergeInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        let left_comp = data.path.nodes[data.hit_comp_idx].get_comp();
        let last_comp_ref = data.path.nodes.last().unwrap().get_comp();

        if data.right_matched.len() == 1 {
            let right_match = *data.right_matched.first().unwrap();
            // only try complex merges

            let complex_merge = left_comp.graph().nodes().all(|left_match| {
                let graph_with_matching = get_local_merge_graph(
                    left_comp,
                    last_comp_ref,
                    &vec![(left_match, right_match)],
                );

                prove_via_direct_merge(
                    &graph_with_matching,
                    vec![left_comp, last_comp_ref],
                    context.credit_inv.clone(),
                    &mut ProofNode::new_any(String::new()),
                )
            });

            if complex_merge {
                return ProofNode::new_leaf(format!("Complex Merge possible"), true);
            }
        }
        return ProofNode::new_leaf(format!("Complex Merge failed"), false);
    }
}

impl From<NPCEnumOutput<MatchingNodesEnumeratorOutput>> for LocalMergeInput {
    fn from(o: NPCEnumOutput<MatchingNodesEnumeratorOutput>) -> Self {
        LocalMergeInput {
            left_comp: o.input.left_comp,
            right_comp: o.input.last_comp,
            left_matched: o.input.left_matched,
            right_matched: o.input.right_matched,
            np_config_left: o.npc,
            np_config_right: o.input.npc_last,
        }
    }
}

pub struct LocalMergeInput {
    left_comp: Component,
    right_comp: Component,
    left_matched: Vec<u32>,
    right_matched: Vec<u32>,
    np_config_left: NicePairConfig,
    np_config_right: NicePairConfig,
}

pub struct LocalMerge;

impl Tactic for LocalMerge {
    type In = LocalMergeInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        let matching = data
            .left_matched
            .iter()
            .zip(data.right_matched.iter())
            .map(|(l, r)| (*l, *r))
            .collect_vec();
        let graph_with_matching =
            get_local_merge_graph(&data.left_comp, &data.right_comp, &matching);

        let total_comp_credit = context.credit_inv.credits(&data.left_comp)
            + context.credit_inv.credits(&data.right_comp);

        if data.left_comp.is_complex() || data.right_comp.is_complex() {
            for sell in edges_of_type(&graph_with_matching, EdgeType::Sellable)
                .into_iter()
                .powerset()
            {
                let sell_credits = Credit::from_integer(sell.len() as i64);
                let mut total_plus_sell = total_comp_credit + sell_credits;

                for buy in matching
                    .iter()
                    .cloned()
                    .powerset()
                    .filter(|p| !p.is_empty())
                {
                    let buy_credits = Credit::from_integer(buy.len() as i64);

                    let check_graph = EdgeFiltered::from_fn(&graph_with_matching, |(v1, v2, t)| {
                        if t == &EdgeType::Sellable && sell.contains(&(v1, v2))
                            || sell.contains(&(v2, v1))
                        {
                            false
                        } else if t == &EdgeType::Buyable
                            && !buy.contains(&(v1, v2))
                            && !buy.contains(&(v2, v1))
                        {
                            false
                        } else {
                            true
                        }
                    });

                    if buy.len() == 2
                        && !(data.left_comp.is_complex() && data.right_comp.is_complex())
                    {
                        let l1 = buy[0].0;
                        let r1 = buy[0].1;
                        let l2 = buy[1].0;
                        let r2 = buy[1].1;

                        if !data.left_comp.is_adjacent(l1, l2)
                            && data.np_config_left.is_nice_pair(l1, l2)
                        {
                            total_plus_sell += Credit::from_integer(1)
                        }
                        if !data.right_comp.is_adjacent(r1, r2)
                            && data.np_config_right.is_nice_pair(r1, r2)
                        {
                            total_plus_sell += Credit::from_integer(1)
                        }
                    }

                    match is_complex(&check_graph) {
                        ComplexCheckResult::Complex(bridges, black_vertices) => {
                            let blocks_graph = EdgeFiltered::from_fn(&check_graph, |(v, u, _)| {
                                !bridges.contains(&(v, u)) && !bridges.contains(&(u, v))
                            });
                            let num_blocks =
                                connected_components(&blocks_graph) - black_vertices.len();
                            let black_deg: usize = black_vertices
                                .iter()
                                .map(|v| bridges.iter().filter(|(a, b)| a == v || b == v).count())
                                .sum();
                            let new_credits = Credit::from_integer(num_blocks as i64)
                                * context.credit_inv.complex_block()
                                + context.credit_inv.complex_black(black_deg as i64)
                                + context.credit_inv.complex_comp();

                            if total_plus_sell - buy_credits >= new_credits {
                                return ProofNode::new_leaf("Local merge to complex".into(), true);
                            }
                        }
                        ComplexCheckResult::NoBridges => {
                            if total_plus_sell - buy_credits >= context.credit_inv.large() {
                                return ProofNode::new_leaf("Local merge to large".into(), true);
                            }
                        }
                        ComplexCheckResult::BlackLeaf => continue,
                        ComplexCheckResult::NotConnected | ComplexCheckResult::Empty => continue,
                    }
                }
            }
        } else {
            for buy in matching.into_iter().powerset().filter(|p| p.len() == 2) {
                let l1 = buy[0].0;
                let r1 = buy[0].1;
                let l2 = buy[1].0;
                let r2 = buy[1].1;

                let mut credits = total_comp_credit - Credit::from_integer(2);

                if data.np_config_left.is_nice_pair(l1, l2) {
                    credits += Credit::from_integer(1)
                }
                if data.np_config_right.is_nice_pair(r1, r2) {
                    credits += Credit::from_integer(1)
                }

                if credits >= context.credit_inv.large() {
                    return ProofNode::new_leaf("Local merge to large".into(), true);
                }
            }
        }

        return ProofNode::new_leaf("Local merge impossible".into(), false);
    }
}

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
            if (data.last.is_c3() || data.last.is_c4() || data.last.is_c5() || data.last.is_complex())
                && !data.np_config_last.is_nice_pair(m_other.1, m_outside.source())
            {
                return ProofNode::new_leaf("No longer path via swapping matching edges: no nice pairs".into(), false)
            }

            // Now if C_l-1 does not care about nice pairs, we are done!
            if data.prelast.is_c6() || data.prelast.is_large() {
                return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true)
            }

            // For others, we have to check that swaping the path edges keeps a nice pair
            if data.prelast
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
                return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true)

            }
            return ProofNode::new_leaf("No longer path via swapping matching edges: no swapping".into(), false)

        } else {
            return ProofNode::new_leaf("No longer path via swapping matching edges: no preconditions".into(), false)
        }
    }
}



impl From<NPCEnumOutput<MatchingHitEnumeratorOutput>> for CycleMergeInput {
    fn from(o: NPCEnumOutput<MatchingHitEnumeratorOutput>) -> Self {
        CycleMergeInput {
            path: o.input.nice_path,
            m_last: o.input.three_matching,
            np_config_last: o.npc,
        }
    }
}

pub struct CycleMergeInput {
    path: NicePath,
    m_last: ThreeMatching,
    np_config_last: NicePairConfig,
}

pub struct CycleMerge;

impl Tactic for CycleMerge {
    type In = CycleMergeInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        // If we land here, we want that at least one matching edge hits C_j for j <= l - 2.
        if !(matches!(data.m_last.1.hit(), PathMatchingHits::Path(j) if j <= context.path_len - 3)
            || matches!(data.m_last.2.hit(), PathMatchingHits::Path(j) if j <= context.path_len - 3))
        {
            return ProofNode::new_leaf(format!("There are no matching edges forming cycles! Aborting"),
            false)
        }

        let mut case_path = data.path.clone();
        *case_path.nodes.last_mut().unwrap() = SuperNode::Zoomed(ZoomedNode {
            comp: case_path.nodes.last().unwrap().get_comp().clone(),
            in_node: Some(data.m_last.0.source()),
            out_node: None,
            npc: data.np_config_last.clone(),
        });

        let mut proof = ProofNode::new_any("Any cycle merge".into());

        // Try worst-case merge
        // TODO also good cases and then exclude the rest
        let mut cases_remain: Vec<MergeCases> = vec![];
        for m_edge in vec![data.m_last.1, data.m_last.2]
            .into_iter()
            .filter(|m_edge| matches!(m_edge.hit(), PathMatchingHits::Path(r) if r <= context.path_len - 3))
        {
            if check_nice_path_with_cycle(
                &case_path,
                m_edge,
                false,
                context.credit_inv.clone(),
                &mut proof,
            ) {
                return proof;
            } else if check_nice_path_with_cycle(
                &case_path,
                m_edge,
                true,
                context.credit_inv.clone(),
                &mut proof,
            ) {
                cases_remain.push(MergeCases::NoNicePair(m_edge))
                // it remains to check merge for non-nice pair hit
            } else {
                cases_remain.push(MergeCases::NoNicePair(m_edge));
                cases_remain.push(MergeCases::NicePair(m_edge));
                // it remains to check merge for nice pair and non-nice pair
            }
        }

        proof.add_child(ProofNode::new_leaf("Tactics exhausted".into(), false));

        proof

    }
}









// Private tactics (subroutines)

#[derive(Clone)]
struct LongerNicePathCheckInput<'a> {
    last_comp_ref: &'a Component,
    np_config: &'a NicePairConfig,
    last_pseudo_edge: &'a PathMatchingEdge,
}

struct LongerNicePathCheck<'a> {
    other_matching_edge: &'a PathMatchingEdge,
}

impl<'a> LongerNicePathCheck<'a> {
    fn check_for(other_matching_edge: &'a PathMatchingEdge) -> Self {
        LongerNicePathCheck {
            other_matching_edge,
        }
    }
}

impl<'a> Tactic for LongerNicePathCheck<'a> {
    type In = LongerNicePathCheckInput<'a>;

    fn action(&self, data: Self::In, context: &ProofContext) -> crate::proof_tree::ProofNode {
        if data.last_comp_ref.is_c6()
            || data.last_comp_ref.is_large()
            || data.np_config.is_nice_pair(
                data.last_pseudo_edge.source(),
                self.other_matching_edge.source(),
            )
        {
            ProofNode::new_leaf(
                format!(
                    "Longer nice path found via edge ({})!",
                    self.other_matching_edge
                ),
                true,
            )
        } else {
            ProofNode::new_leaf(
                format!(
                    "No longer nice path possible via edge ({})!",
                    self.other_matching_edge
                ),
                false,
            )
        }
    }
}
