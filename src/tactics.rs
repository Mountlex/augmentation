use itertools::Itertools;
use petgraph::{visit::EdgeFiltered, algo::connected_components};

use crate::{
    comps::{Component, Node, edges_of_type, CreditInvariant, EdgeType},
    enumerators::{ComponentHitOutput, MatchingHitEnumeratorOutput, NPCEnumOutput, MatchingNodesEnumeratorOutput},
    local_merge::prove_via_direct_merge,
    nice_path::{
        get_local_merge_graph, or, NicePairConfig, NicePath, PathMatchingEdge, ProofContext, Tactic,
    },
    proof_tree::ProofNode, Credit, bridges::{is_complex, ComplexCheckResult},
};

impl From<NPCEnumOutput<MatchingHitEnumeratorOutput>> for LongerPathInput {
    fn from(o: NPCEnumOutput<MatchingHitEnumeratorOutput>) -> Self {
        LongerPathInput {
            nice_path: o.input.nice_path,
            m_path: o.input.m_path,
            m1: o.input.m1,
            m2: o.input.m2,
            npc: o.npc,
        }
    }
}

pub struct LongerPathInput {
    nice_path: NicePath,
    m_path: PathMatchingEdge,
    m1: PathMatchingEdge,
    m2: PathMatchingEdge,
    npc: NicePairConfig,
}

pub struct LongerPathTactic;

impl Tactic for LongerPathTactic {
    type In = LongerPathInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> crate::proof_tree::ProofNode {
        let check_input = LongerNicePathCheckInput {
            last_comp_ref: data.nice_path.nodes.last().unwrap().get_comp(),
            np_config: &data.npc,
            last_pseudo_edge: &data.m_path,
        };

        if data.m1.hits_outside() && data.m2.hits_outside() {
            or(
                LongerNicePathCheck::check_for(&data.m1),
                LongerNicePathCheck::check_for(&data.m2),
            )
            .action(check_input, context)
        } else if data.m1.hits_outside() {
            LongerNicePathCheck::check_for(&data.m1).action(check_input, context)
        } else if data.m2.hits_outside() {
            LongerNicePathCheck::check_for(&data.m2).action(check_input, context)
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
        LocalMergeInput { left_comp: o.input.left_comp, right_comp: o.input.last_comp, left_matched: o.input.left_matched, right_matched: o.input.right_matched, np_config_left: o.npc, np_config_right: o.input.npc_last }
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
        let matching = data.left_matched
            .iter()
            .zip(data.right_matched.iter())
            .map(|(l, r)| (*l, *r))
            .collect_vec();
        let graph_with_matching = get_local_merge_graph(&data.left_comp, &data.right_comp, &matching);

        let total_comp_credit = context.credit_inv.credits(&data.left_comp) + context.credit_inv.credits(&data.right_comp);

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

                    if buy.len() == 2 && !(data.left_comp.is_complex() && data.right_comp.is_complex()) {
                        let l1 = buy[0].0;
                        let r1 = buy[0].1;
                        let l2 = buy[1].0;
                        let r2 = buy[1].1;

                        if !data.left_comp.is_adjacent(l1, l2) && data.np_config_left.is_nice_pair(l1, l2) {
                            total_plus_sell += Credit::from_integer(1)
                        }
                        if !data.right_comp.is_adjacent(r1, r2) && data.np_config_right.is_nice_pair(r1, r2) {
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

        return ProofNode::new_leaf("Local merge impossible".into(), false)
    }
}


pub struct LongerNicePathViaMatchingSwapInput {
    left_comp: Component,
    right_comp: Component,
    left_matched: Vec<u32>,
    right_matched: Vec<u32>,
    np_config_left: NicePairConfig,
    np_config_right: NicePairConfig,
}


pub struct LongerNicePathViaMatchingSwap;

impl Tactic for LongerNicePathViaMatchingSwap {
    type In = LongerNicePathViaMatchingSwapInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        //  TODO Longer path if local merge not possible
        if data.left_matched.len() == 2
        && (m1.hits_outside() || m2.hits_outside())
        && (m1.hits_path() == Some(path_len - 2)
            || m2.hits_path() == Some(path_len - 2))
    {
        let m_outside = vec![m1, m2]
            .into_iter()
            .find(|&m| m.hits_outside())
            .unwrap();
        let (m_path, m_other) =
            if right_matched[0] == m_path.source() {
                (
                    Edge(left_matched[0], right_matched[0]),
                    Edge(left_matched[1], right_matched[1]),
                )
            } else {
                (
                    Edge(left_matched[1], right_matched[1]),
                    Edge(left_matched[0], right_matched[0]),
                )
            };

        if longer_nice_path_via_matching_swap(
            left_comp,
            &np_config_last,
            last_comp_ref,
            m_path,
            m_other,
            m_outside,
        ) {
            return true;
        }
    }

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
