use itertools::Itertools;
use petgraph::{algo::connected_components, visit::EdgeFiltered};

use crate::{
    bridges::{has_at_least_one_bridge, is_complex, ComplexCheckResult},
    comps::{edges_of_type, EdgeType},
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
    tree::{utils::get_merge_graph, TreeCaseInstance, TreeContext},
    types::Edge,
    Credit, CreditInv, Graph, Node,
};

pub struct DirectMerge {
    num_calls: usize,
    num_proofs: usize,
}

impl DirectMerge {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for DirectMerge {
    fn print_stats(&self) {
        println!("Direct merge {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<TreeCaseInstance, TreeContext> for DirectMerge {
    fn action(&mut self, data: &TreeCaseInstance, context: &TreeContext) -> ProofNode {
        self.num_calls += 1;

        if data
            .comps
            .windows(2)
            .any(|w| w[0].is_large() && w[1].is_large())
        {
            return ProofNode::new_leaf("Direct merge between two Large".into(), true);
        }

        let graph = get_merge_graph(&data.comps, &data.edges);

        let sellable = edges_of_type(&graph, EdgeType::Sellable)
            .into_iter()
            .map(|(u, v)| Edge::from_tuple(u, v));
        let buyable = edges_of_type(&graph, EdgeType::Buyable)
            .into_iter()
            .map(|(u, v)| Edge::from_tuple(u, v));

        let total_component_credits = data
            .comps
            .iter()
            .map(|c| context.credit_inv.credits(c))
            .sum();

        let one_is_complex = data.comps.iter().any(|c| c.is_complex());
        let result = find_feasible_merge(
            &graph,
            buyable.powerset().filter(|p| {
                if one_is_complex {
                    p.len() >= (data.comps.len() - 1)
                } else {
                    p.len() >= 2 * (data.comps.len() - 1)
                }
            }),
            sellable.powerset(),
            total_component_credits,
            data.comps.iter().map(|c| c.num_edges()).sum(),
            &context.credit_inv,
            one_is_complex,
        );

        match result {
            MergeResult::Feasible2EC(merge) => {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!(
                        "Direct merge to 2EC possible [bought = {}, sold = {}]",
                        merge.bought_edges.iter().join(", "),
                        merge.sold_edges.iter().join(", ")
                    ),
                    true,
                );
            }
            MergeResult::FeasibleComplex(merge) => {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!(
                        "Direct merge to complex possible [bought = {}, sold = {}]",
                        merge.bought_edges.iter().join(", "),
                        merge.sold_edges.iter().join(", ")
                    ),
                    true,
                );
            }
            MergeResult::Impossible => {
                return ProofNode::new_leaf(
                    format!(
                        "Direct merge impossible [available credits: {}]",
                        total_component_credits
                    ),
                    false,
                );
            }
        }
    }
}

pub struct FeasibleMerge {
    bought_edges: Vec<Edge>,
    sold_edges: Vec<Edge>,
    new_comp_credit: Credit,
}

pub enum MergeResult {
    Feasible2EC(FeasibleMerge),
    FeasibleComplex(FeasibleMerge),
    Impossible,
}

fn find_feasible_merge<'a, B, S>(
    graph: &Graph,
    buy_iter: B,
    sell_iter: S,
    total_component_credits: Credit,
    num_comp_edges: usize,
    credit_inv: &CreditInv,
    one_is_complex: bool,
) -> MergeResult
where
    B: Iterator<Item = Vec<Edge>> + Clone,
    S: Iterator<Item = Vec<Edge>>,
{
    let req_credits = credit_inv.two_ec_credit(num_comp_edges);
    let white_vertices = graph
        .nodes()
        .filter(|n| matches!(n, Node::Comp(_)))
        .collect_vec();

    for sell in sell_iter {
        let sell_credits = Credit::from_integer(sell.len() as i64);
        let total_plus_sell = total_component_credits + sell_credits;

        for buy in buy_iter.clone() {
            let buy_credits = Credit::from_integer(buy.len() as i64);

            let check_graph = EdgeFiltered::from_fn(graph, |(v1, v2, t)| {
                if t == &EdgeType::Sellable && sell.contains(&Edge::from_tuple(v1, v2)) {
                    false
                } else if t == &EdgeType::Buyable && !buy.contains(&Edge::from_tuple(v1, v2)) {
                    false
                } else {
                    true
                }
            });

            if !one_is_complex {
                if total_plus_sell - buy_credits >= req_credits {
                    if connected_components(&check_graph) == 1 {
                        if has_at_least_one_bridge(&check_graph) {
                            continue;
                        } else {
                            return MergeResult::Feasible2EC(FeasibleMerge {
                                bought_edges: buy.clone(),
                                sold_edges: sell.clone(),
                                new_comp_credit: req_credits,
                            });
                        }
                    } else {
                        continue;
                    }
                } else {
                    continue;
                }
            } else {
                match is_complex(&check_graph, &white_vertices) {
                    ComplexCheckResult::Complex(bridges, black_vertices) => {
                        let blocks_graph = EdgeFiltered::from_fn(&check_graph, |(v, u, _)| {
                            !bridges.contains(&(v, u)) && !bridges.contains(&(u, v))
                        });
                        let num_blocks = connected_components(&blocks_graph) - black_vertices.len();
                        let black_deg: usize = black_vertices
                            .iter()
                            .map(|v| bridges.iter().filter(|(a, b)| a == v || b == v).count())
                            .sum();
                        let new_credits = Credit::from_integer(num_blocks as i64)
                            * credit_inv.complex_block()
                            + credit_inv.complex_black(black_deg as i64)
                            + credit_inv.complex_comp();

                        if total_plus_sell - buy_credits >= new_credits {
                            //dbg!(bridges);
                            //dbg!(num_blocks);
                            //dbg!(black_vertices);
                            //dbg!(black_deg);

                            return MergeResult::FeasibleComplex(FeasibleMerge {
                                bought_edges: buy.clone(),
                                sold_edges: sell.clone(),
                                new_comp_credit: new_credits,
                            });
                        }
                    }
                    ComplexCheckResult::NoBridges => {
                        if total_plus_sell - buy_credits >= req_credits {
                            return MergeResult::Feasible2EC(FeasibleMerge {
                                bought_edges: buy.clone(),
                                sold_edges: sell.clone(),
                                new_comp_credit: req_credits,
                            });
                        }
                    }
                    ComplexCheckResult::BlackLeaf => continue,
                    ComplexCheckResult::NotConnected | ComplexCheckResult::Empty => continue,
                }
            }
        }
    }
    return MergeResult::Impossible;
}
