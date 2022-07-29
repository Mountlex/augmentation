
use itertools::Itertools;
use num_rational::Rational64;
use petgraph::algo::connected_components;
use petgraph::dot::{Config, Dot};

use crate::bridges::has_bridges;
use crate::comps::*;

mod bridges;
mod comps;


fn main() {
    enumerate_and_check(Rational64::new(1, 3))
}

fn enumerate_and_check(c: Rational64) {
    let graphs = vec![three_cycle(), four_cycle(), five_cycle(), large_component()];

    // Enumerate every graph combination
    for left in graphs.clone() {
        let left_edges = left.edge_list();
        let n_left = Graph::from_edges(&left_edges).node_count() as u32;
        for right in graphs.clone() {
            let mut right_edges = right.edge_list();
            right_edges.iter_mut().for_each(|(w1, w2, _)| {
                *w1 += n_left;
                *w2 += n_left
            });

            let left_nodes: Vec<u32> = Graph::from_edges(&left_edges).nodes().collect();
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
                        let credits = left.credits(c) + right.credits(c);
                        check_credit_invariant(graph, matching, credits);
                    }
                }
            }

            // If we found shortcuts for every matching, this combination is valid
            println!("Checked  {} and {}!", left, right);
        }
    }
}

fn check_credit_invariant(graph: Graph, matching: EdgeList, credits: Rational64) {
    let shortcutable: Vec<(u32, u32, &EdgeType)> = graph
        .all_edges()
        .filter(|(_, _, t)| **t == EdgeType::One)
        .collect();

    for buy in matching.iter().powerset().filter(|p| p.len() >= 2) {
        for shortcut in shortcutable.iter().powerset() {
            let s = Rational64::from_integer(shortcut.len() as i64);
            let b = Rational64::from_integer(buy.len() as i64);
            let mut graph_copy = graph.clone();
            for (u, v, _) in &shortcut {
                graph_copy.remove_edge(*u, *v);
            }
            for (u, v, _) in &buy {
                graph_copy.add_edge(*u, *v, EdgeType::One);
            }

            if connected_components(&graph_copy) > 1 {
                continue;
            }

            if !has_bridges(&graph_copy) {
                if credits - b + s >= Rational64::from_integer(2) {
                    return;
                } else {
                    //println!("Shortcut: {:?}. no bridges, but credit {} - {} + {}", shortcut, credits, b, s);
                }
            }
        }
    }

    println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
    panic!("Graph cannot be shortcutted!");
}
