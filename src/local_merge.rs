use itertools::{iproduct, Itertools};
use num_rational::Rational64;
use petgraph::visit::{IntoNodeReferences, EdgeFiltered, NodeCount};
use rayon::prelude::*;
use std::fmt::Display;

use crate::{
    bridges::no_bridges_and_connected,
    comps::{Component, CreditInvariant, EdgeType, Graph, Node},
    edges_of_type, merge_to_base, Credit,
};

pub fn prove_all_local_merges<C: CreditInvariant + Sync>(comps: Vec<Component>, credit_inv: C, depth: usize) {
    // Enumerate every graph combination and prove merge
    let combinations: Vec<(&Component, &Component)> = iproduct!(&comps, &comps).collect_vec();
    combinations.into_iter().for_each(|(left, right)| {
        log::info!("Proving local merge between {} and {} ...", left, right);
        let left_graph = left.graph();
        let left_nodes = left_graph.nodes().collect();
        if prove_local_merge(
            left_graph,
            credit_inv.credits(left),
            left_nodes,
            &right,
            &comps,
            credit_inv.clone(),
            depth
        ) {
            log::info!("✔️ Proved local merge between {} and {} ", left, right);
        } else {
            log::warn!("❌ Disproved local merge between {} and {} ", left, right);
        }
    });
}

#[derive(Clone, Debug)]
struct Matching<'a> {
    edges: Vec<(Node, Node)>,
    graph_nodes: Vec<&'a Vec<Node>>,
}

impl Display for Matching<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (v1, v2) in &self.edges {
            let c1 = self.graph_nodes.iter().find(|c| c.contains(v1)).unwrap();
            let p1 = c1.iter().position(|v| v == v1).unwrap();
            let c2 = self.graph_nodes.iter().find(|c| c.contains(v2)).unwrap();
            let p2 = c2.iter().position(|v| v == v2).unwrap();
            write!(f, "(v{},u{}),", p1, p2)?;
        }
        write!(f, "}}")
    }
}

fn prove_local_merge_between_three<C: CreditInvariant>(
    left: &Component,
    middle: &Component,
    graph: Graph,
    left_nodes: Vec<Node>,
    middle_nodes: Vec<Node>,
    left_matching: Matching,
    comps: &Vec<Component>,
    credit_inv: C,
) -> bool {
    for right in comps {
        // log::trace!(
        //     "   Proving merge between {} and {} and {} ...",
        //     left,
        //     middle,
        //     right
        // );
        let right_graph = right.graph();
        let (graph, nodes) = merge_to_base(graph.clone(), vec![&right_graph]);
        let right_nodes = &nodes[0];
        let previous_credits =
            credit_inv.credits(left) + credit_inv.credits(middle) + credit_inv.credits(right);

        for right_matched in right_nodes.iter().powerset().filter(|p| p.len() == 3) {
            for middle_right_matched in middle_nodes.iter().powerset().filter(|p| p.len() == 3) {
                for middle_right_perm in middle_right_matched.into_iter().permutations(3) {
                    let mut right_matching = Matching {
                        edges: right_matched
                            .iter()
                            .zip(middle_right_perm.into_iter())
                            .map(|(&l, r)| (*l, *r))
                            .collect(),
                        graph_nodes: vec![&left_nodes, &middle_nodes, &right_nodes],
                    };

                    right_matching
                        .edges
                        .append(&mut left_matching.edges.clone());

                    let prove_simple_merge = find_local_merge_with_matching(
                        &graph,
                        credit_inv.clone(),
                        previous_credits,
                    );

                    if !prove_simple_merge {
                        log::trace!(
                            "   disproved merge between {} and {} and {} ❌ ",
                            left,
                            middle,
                            right
                        );
                        return false;
                    }
                }
            }
        }
        log::trace!(
            "   Proved merge between {} and {} and {} ✔️",
            left,
            middle,
            right
        );
    }
    true
}

fn prove_local_merge<C: CreditInvariant>(
    left: Graph,
    left_comp_credit: Credit,
    left_matching_end: Vec<Node>,
    right: &Component,
    comps: &Vec<Component>,
    credit_inv: C,
    depth: usize,
) -> bool {
    let right_graph = right.graph();
    // Build combined graph
    let (graph, nodes) = merge_to_base(left, vec![&right_graph]);
    let right_nodes = &nodes[0];

    let previous_credits = left_comp_credit + credit_inv.credits(right);

    // Enumerate all possible matchings (adversarial)
    for left_matched in left_matching_end.iter().powerset().filter(|p| p.len() == 3) {
        let right_iter: Vec<Vec<&u32>> = match right {
            Component::Simple(_) => right_nodes.iter().permutations(3).map(|p| p).collect(),
            Component::Large => vec![right_nodes.iter().collect()],
        };
        for perm in right_iter {
            // Compute edges of matching
            let matching = Matching {
                edges: left_matched
                    .iter()
                    .zip(perm.into_iter())
                    .map(|(l, r)| (**l, *r))
                    .collect(),
                graph_nodes: vec![&left_matching_end, &right_nodes],
            };

            let mut matching_graph = graph.clone();
            for (m1, m2) in &matching.edges {
                matching_graph.add_edge(*m1, *m2, EdgeType::Buyable);
            }

            let proved = find_local_merge_with_matching(
                &matching_graph,
                credit_inv.clone(),
                previous_credits,
            );

            if !proved {
                if depth == 0 {
                    return false;
                }
                for next in comps {
                    if !prove_local_merge(
                        matching_graph.clone(),
                        previous_credits,
                        right_nodes.clone(),
                        next,
                        comps,
                        credit_inv.clone(),
                        depth - 1,
                    ) {
                        return false;
                    }
                }
            }
        }
    }

    true

    // If we found shortcuts for every matching, this combination is valid
}

fn find_local_merge_with_matching<C: CreditInvariant>(
    graph: &Graph,
    credit_inv: C,
    previous_credits: Rational64,
) -> bool {

    let sellable = edges_of_type(graph, EdgeType::Sellable);
    let buyable = edges_of_type(graph, EdgeType::Buyable);

    //dbg!(&buyable);
    //dbg!(&sellable);

    let result = enumerate_and_check(
        graph,
        buyable.into_iter()
            .powerset()
            .filter(|p| p.len() >= 2),
        sellable
            .into_iter()
            .powerset(),
        credit_inv,
        previous_credits,
    );

    if !result {
        log::trace!(
            "   Couldn't find local merge with matching edges "
        );
    }

    result
}

pub fn enumerate_and_check<'a, B, S, C: CreditInvariant>(
    graph: &Graph,
    buy_iter: B,
    sell_iter: S,
    credit_inv: C,
    previous_credits: Rational64,
) -> bool
where
    B: Iterator<Item = Vec<(u32, u32)>> + Clone,
    S: Iterator<Item = Vec<(u32, u32)>>,
{
    for sell in sell_iter {
        for buy in buy_iter.clone() {
            let buy_credits = Rational64::from_integer(buy.len() as i64);
            let sell_credits = Rational64::from_integer(sell.len() as i64);

            let check_graph = EdgeFiltered::from_fn(graph, |(v1,v2,t)| {
                if t == &EdgeType::Sellable && sell.contains(&(v1,v2)) || sell.contains(&(v2,v1)) {
                    false
                } else if t == &EdgeType::Buyable && !buy.contains(&(v1,v2)) && !buy.contains(&(v2,v1)) {
                    false
                } else {
                    true
                }
            });

          
            if no_bridges_and_connected(&check_graph) {
                if previous_credits - buy_credits + sell_credits
                    >= credit_inv.credits(&Component::Large)
                {
                    //println!("Sell {:?}", sell);
                    //println!("Credits = {} - {} + {}", previous_credits, buy_credits, sell_credits);
                    return true;
                } else {
                    //println!("Shortcut: {:?}. no bridges, but credit {} - {} + {}", shortcut, credits, b, s);
                }
            }
        }
    }
    false
}
