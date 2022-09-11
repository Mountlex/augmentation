use itertools::Itertools;
use petgraph::{algo::connected_components, visit::EdgeFiltered};

use crate::{
    bridges::{is_complex, ComplexCheckResult},
    comps::{edges_of_type, Component, CreditInvariant, EdgeType},
    path::{
        enumerators::{matching_nodes::MatchingNodesEnumeratorOutput, nice_pairs::NPCEnumOutput},
        proof::{ProofContext, Tactic},
        utils::get_local_merge_graph,
        NicePairConfig,
    },
    proof_tree::ProofNode,
    Credit,
};

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
