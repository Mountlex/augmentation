use itertools::Itertools;
use petgraph::{algo::connected_components, visit::EdgeFiltered};

use crate::{
    bridges::{is_complex, ComplexCheckResult},
    comps::{edges_of_type, EdgeType},
    path::Pidx,
    proof_logic::{Statistics, Tactic},
    proof_tree::DefaultProofNode,
    tree::{utils::get_merge_graph, TreeCaseInstance, TreeContext},
    types::Edge,
    Credit, CreditInv, Graph, Node,
};

pub struct DirectMerge {
    num_calls: usize,
    num_proofs: usize,
    name: String,
}

impl DirectMerge {
    pub fn new(name: String) -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
            name,
        }
    }
}

impl Statistics for DirectMerge {
    fn print_stats(&self) {
        println!("{} {} / {}", self.name, self.num_proofs, self.num_calls);
    }
}

impl Tactic<TreeCaseInstance, TreeContext> for DirectMerge {
    fn action(&mut self, data: &TreeCaseInstance, context: &TreeContext) -> DefaultProofNode {
        self.num_calls += 1;

        if data
            .comps
            .windows(2)
            .any(|w| w[0].is_large() && w[1].is_large())
        {
            return DefaultProofNode::new_leaf("Direct merge between two Large".into(), true);
        }

        let graph = get_merge_graph(&data.comps, &data.edges);

        let sellable = edges_of_type(&graph, EdgeType::Sellable)
            .into_iter()
            .map(|(u, v)| Edge::from_tuple(u, v));
        let buyable = data.edges.iter().cloned();

        let total_component_credits = data
            .comps
            .iter()
            .map(|c| context.credit_inv.credits(c))
            .sum();

        let one_is_complex = data.comps.iter().any(|c| c.is_complex());
        let buy_endpoints = edges_of_type(&graph, EdgeType::Buyable)
            .into_iter()
            .flat_map(|e| vec![e.0, e.1])
            .collect_vec();

        let result = find_feasible_merge(
            &graph,
            buyable.powerset().filter(|p| {
                (0..data.comps.len()).tuple_windows().all(|(l, r)| {
                    let bound = if data.comps[l].is_complex() || data.comps[r].is_complex() {
                        1
                    } else {
                        2
                    };
                    p.iter()
                        .filter(|e| e.between_path_nodes(Pidx::from(l), Pidx::from(r)))
                        .count()
                        >= bound
                })
                // if one_is_complex {
                //     p.len() >= (data.comps.len() - 1)
                // } else {
                //     p.len() >= 2 * (data.comps.len() - 1)
                // }
            }),
            sellable
                .filter(|e| e.nodes_incident(&buy_endpoints))
                .powerset()
                .filter(|p| p.len() <= 2 * (data.comps.len() - 1)),
            total_component_credits,
            data.comps.iter().map(|c| c.num_edges()).sum(),
            &context.credit_inv,
            one_is_complex,
        );

        match result {
            MergeResult::Feasible2EC(merge) => {
                self.num_proofs += 1;
                return DefaultProofNode::new_leaf(
                    format!(
                        "Direct merge to 2EC possible [bought = {}, sold = {}, new = {}]",
                        merge.bought_edges.iter().join(", "),
                        merge.sold_edges.iter().join(", "),
                        merge.new_comp_credit
                    ),
                    true,
                );
            }
            MergeResult::FeasibleComplex(merge) => {
                self.num_proofs += 1;
                return DefaultProofNode::new_leaf(
                    format!(
                        "Direct merge to complex possible [bought = {}, sold = {}, new = {}]",
                        merge.bought_edges.iter().join(", "),
                        merge.sold_edges.iter().join(", "),
                        merge.new_comp_credit
                    ),
                    true,
                );
            }
            MergeResult::Impossible => {
                return DefaultProofNode::new_leaf(
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
    B: Iterator<Item = Vec<Edge>>,
    S: Iterator<Item = Vec<Edge>> + Clone,
{
    let req_credits = credit_inv.two_ec_credit(num_comp_edges);
    let white_vertices = graph
        .nodes()
        .filter(|n| matches!(n, Node::Comp(_)))
        .collect_vec();

    for buy in buy_iter {
        let buy_endpoints = buy.iter().flat_map(|e| e.to_vec()).collect_vec();
        for sell in sell_iter.clone().filter(|sell| {
            sell.iter()
                .all(|e| e.between_sets(&buy_endpoints, &buy_endpoints) || one_is_complex)
        }) {
            let sell_credits = Credit::from_integer(sell.len() as i64);
            let buy_credits = Credit::from_integer(buy.len() as i64);
            let total = total_component_credits + sell_credits - buy_credits;

            let check_graph = EdgeFiltered::from_fn(graph, |(v1, v2, t)| {
                if t == &EdgeType::Sellable && sell.contains(&Edge::from_tuple(v1, v2)) {
                    false
                } else if t == &EdgeType::Buyable && !buy.contains(&Edge::from_tuple(v1, v2)) {
                    false
                } else {
                    true
                }
            });

            //println!("sell {}", sell.iter().join(","));
            //println!("buy {}", buy.iter().join(","));

            if !one_is_complex {
                if total >= req_credits {
                    if connected_components(&check_graph) == 1 {
                        if is_complex(&check_graph, &vec![], true).has_bridges() {
                            continue;
                        } else {
                            return MergeResult::Feasible2EC(FeasibleMerge {
                                bought_edges: buy.clone(),
                                sold_edges: sell.clone(),
                                new_comp_credit: req_credits,
                            });
                        }
                    } else {
                        // println!("{:?}", sell);
                        // println!("{:?}", buy);
                        // println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
                        // panic!();
                        continue;
                    }
                } else {
                    continue;
                }
            } else {
                match is_complex(&check_graph, &white_vertices, false) {
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

                        if total >= new_credits {
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
                        if total >= req_credits {
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
