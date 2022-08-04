use itertools::Itertools;
use num_rational::Rational64;
use petgraph::algo::connected_components;
use petgraph::dot::{Config, Dot};

use crate::bridges::compute_bridges;
use crate::comps::*;

mod bridges;
mod comps;

fn main() {
    let inv = DefaultCredits::new(Rational64::new(1, 3));
    let comps = vec![three_cycle(), four_cycle(), five_cycle(), large_component()];
    prove_all_local_merges(comps, inv);
}

fn prove_all_local_merges<C: CreditInvariant>(comps: Vec<Component>, credit_inv: C) {
    // Enumerate every graph combination and prove merge
    for left in &comps {
        for right in &comps {
            prove_local_merge(left, right, credit_inv.clone());
        }
    }
}

fn prove_local_merge<C: CreditInvariant>(left: &Component, right: &Component, credit_inv: C) {
    let left_edges = left.edge_list();
    let left_nodes: Vec<u32> = Graph::from_edges(&left_edges).nodes().collect();
    let n_left = left_nodes.len() as u32;
    let mut right_edges = right.edge_list();
    right_edges.iter_mut().for_each(|(w1, w2, _)| {
        *w1 += n_left;
        *w2 += n_left
    });
    let right_nodes: Vec<u32> = Graph::from_edges(&right_edges).nodes().collect();

    // Enumerate all possible matchings (adversarial)
    for left_matched in left_nodes.iter().powerset().filter(|p| p.len() == 3) {
        for right_matched in right_nodes.iter().powerset().filter(|p| p.len() == 3) {
            for right_perm in right_matched.into_iter().permutations(3) {
                // Compute edges of matching
                let matching: EdgeList = left_matched
                    .iter()
                    .zip(right_perm.into_iter())
                    .map(|(&l, r)| (*l, *r, EdgeType::Zero))
                    .collect();

                // Build combined graph
                let graph_edges: EdgeList = vec![left_edges.clone(), right_edges.clone()]
                    .into_iter()
                    .flatten()
                    .collect();
                let graph = Graph::from_edges(&graph_edges);
                let previous_credits = credit_inv.credits(left) + credit_inv.credits(right);

                find_local_merge_with_matching(
                    &graph,
                    matching,
                    credit_inv.clone(),
                    previous_credits,
                )
            }
        }
    }

    // If we found shortcuts for every matching, this combination is valid
    println!("Checked  {} and {}!", left, right);
}

fn find_local_merge_with_matching<C: CreditInvariant>(
    graph: &Graph,
    matching: EdgeList,
    credit_inv: C,
    previous_credits: Rational64,
) {
    let shortcutable: Vec<(u32, u32, &EdgeType)> = graph
        .all_edges()
        .filter(|(_, _, t)| **t == EdgeType::One)
        .collect();

    let result = enumerate_and_check(
        &graph,
        matching.iter().powerset().filter(|p| p.len() >= 2),
        shortcutable.iter().powerset(),
        credit_inv,
        previous_credits,
    );

    if !result {
        println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
        panic!("Graph cannot be shortcutted!");
    }
}

fn enumerate_and_check<'a, B, S, C: CreditInvariant>(
    graph: &Graph,
    buy_iter: B,
    sell_iter: S,
    credit_inv: C,
    previous_credits: Rational64,
) -> bool
where
    B: 'a + Iterator<Item = Vec<&'a (u32, u32, EdgeType)>>,
    S: 'a + Iterator<Item = Vec<&'a (u32, u32, &'a EdgeType)>> + Clone,
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
                    return true;
                } else {
                    //println!("Shortcut: {:?}. no bridges, but credit {} - {} + {}", shortcut, credits, b, s);
                }
            }
        }
    }

    return false;
}
