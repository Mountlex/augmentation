use itertools::Itertools;
use nice_path::prove_nice_path_progress;
use num_rational::Rational64;
use petgraph::algo::connected_components;

use crate::bridges::compute_bridges;
use crate::comps::*;

mod bridges;
mod comps;
mod nice_path;

fn main() {
    let inv = DefaultCredits::new(Rational64::new(1, 3));
    let comps = vec![three_cycle(), four_cycle(), five_cycle(), large_component()];
    prove_all_local_merges(comps.clone(), inv.clone());
    prove_nice_path_progress(comps, inv);
}

fn prove_all_local_merges<C: CreditInvariant>(comps: Vec<Component>, credit_inv: C) {
    // Enumerate every graph combination and prove merge
    for left in &comps {
        for right in &comps {
            if prove_local_merge(left, right, credit_inv.clone()) {
                println!("Local merge between {} and {}: ✔️", left, right);
            } else {
                println!("Local merge between {} and {}: ❌", left, right);
            }
        }
    }
}

pub fn relabel_nodes(graphs: Vec<&mut Graph>) {
    let mut offset = 0;
    for graph in graphs {
        let mut edges: Vec<(u32, u32, &EdgeType)> = graph.all_edges().collect();
        edges.iter_mut().for_each(|(w1, w2, _)| {
            *w1 += offset;
            *w2 += offset
        });
        offset += graph.node_count() as u32;
        *graph = Graph::from_edges(edges);
    }
}

pub fn merge_graphs(graphs: Vec<&Graph>) -> Graph {
    Graph::from_edges(graphs.into_iter().flat_map(|g| g.all_edges()))
}

pub fn edges_of_type<'a>(graph: &'a Graph, typ: EdgeType) -> Vec<(u32, u32, EdgeType)> {
    graph
        .all_edges()
        .filter(|(_, _, t)| **t == typ)
        .map(|(a, b, c)| (a, b, *c))
        .collect()
}

fn prove_local_merge<C: CreditInvariant>(
    left: &Component,
    right: &Component,
    credit_inv: C,
) -> bool {
    let mut left_graph = left.graph();
    let mut right_graph = right.graph();
    relabel_nodes(vec![&mut left_graph, &mut right_graph]);
    // Build combined graph
    let graph = merge_graphs(vec![&left_graph, &right_graph]);
    let previous_credits = credit_inv.credits(left) + credit_inv.credits(right);

    // Enumerate all possible matchings (adversarial)
    for left_matched in left_graph.nodes().powerset().filter(|p| p.len() == 3) {
        for right_matched in right_graph.nodes().powerset().filter(|p| p.len() == 3) {
            for right_perm in right_matched.into_iter().permutations(3) {
                // Compute edges of matching
                let matching: EdgeList = left_matched
                    .iter()
                    .zip(right_perm.into_iter())
                    .map(|(&l, r)| (l, r, EdgeType::Zero))
                    .collect();

                if !find_local_merge_with_matching(
                    &graph,
                    matching,
                    credit_inv.clone(),
                    previous_credits,
                ) {
                    return false;
                }
            }
        }
    }

    true

    // If we found shortcuts for every matching, this combination is valid
}

fn find_local_merge_with_matching<C: CreditInvariant>(
    graph: &Graph,
    matching: EdgeList,
    credit_inv: C,
    previous_credits: Rational64,
) -> bool {
    let m = graph.edge_count();
    let n = graph.node_count();

    let num_matching = matching.len();
    let sellable = edges_of_type(graph, EdgeType::One);

    // if !result {
    //     println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
    //     panic!("Graph cannot be shortcutted!");
    // }

    enumerate_and_check(
        graph,
        matching.into_iter().powerset().filter(|p| p.len() >= 2),
        sellable
            .into_iter()
            .powerset()
            .filter(|p| m + num_matching - p.len() >= n - 1),
        credit_inv,
        previous_credits,
    )
}

fn enumerate_and_check<'a, B, S, C: CreditInvariant>(
    graph: &Graph,
    buy_iter: B,
    sell_iter: S,
    credit_inv: C,
    previous_credits: Rational64,
) -> bool
where
    B: Iterator<Item = Vec<(u32, u32, EdgeType)>>,
    S: Iterator<Item = Vec<(u32, u32, EdgeType)>> + Clone,
{
    for buy in buy_iter {
        for sell in sell_iter.clone() {
            let sell_credits = Rational64::from_integer(sell.len() as i64);
            let buy_credits = Rational64::from_integer(buy.len() as i64);
            let mut graph_copy = graph.clone();
            for (u, v, _) in &sell {
                graph_copy.remove_edge(*u, *v);
            }
            for (u, v, _) in &buy {
                graph_copy.add_edge(*u, *v, EdgeType::One);
            }

            if connected_components(&graph_copy) > 1 {
                continue;
            }

            if compute_bridges(&graph_copy).is_empty() {
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
