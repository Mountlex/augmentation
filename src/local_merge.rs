use itertools::Itertools;
use num_rational::Rational64;

use crate::{comps::{CreditInvariant, Component, EdgeList, EdgeType, Graph}, relabel_nodes, merge_graphs, edges_of_type, enumerate_and_check};


pub fn prove_all_local_merges<C: CreditInvariant>(comps: Vec<Component>, credit_inv: C) {
    // Enumerate every graph combination and prove merge
    for left in &comps {
        for right in &comps {
            if prove_local_merge(left, right, credit_inv.clone()) {
                println!("✔️ Local merge between {} and {}", left, right);
            } else {
                println!("❌ Local merge between {} and {}", left, right);
            }
        }
    }
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