use itertools::Itertools;
use num_rational::Rational64;

use crate::{comps::{CreditInvariant, Component, EdgeList, EdgeType, Graph}, relabel_nodes, merge_graphs, edges_of_type, enumerate_and_check};


pub fn prove_all_local_merges<C: CreditInvariant>(comps: Vec<Component>, credit_inv: C) {
    // Enumerate every graph combination and prove merge
    for left in &comps {
        for right in &comps {
            println!("Local merge between {} and {}", left, right);
            if prove_local_merge(left, right, &comps, credit_inv.clone()) {
                println!("== proved ✔️")
            } else {
                println!("== disproved ❌")
            }
        }
    }
}


fn print_matching(matching: &EdgeList, comps: &Vec<Graph>) {
    for (v1,v2,_) in matching {
        let c1 = comps.iter().find(|c| c.contains_node(*v1)).unwrap();
        let p1 = c1.nodes().position(|v| v == *v1).unwrap();
        let c2 = comps.iter().find(|c| c.contains_node(*v2)).unwrap();
        let p2 = c2.nodes().position(|v| v == *v2).unwrap();
        print!("(v{},u{})",p1,p2);
    } 
}

fn prove_local_merge<C: CreditInvariant>(
    left: &Component,
    middle: &Component,
    comps: &Vec<Component>,
    credit_inv: C,
) -> bool {
    let mut left_graph = left.graph();
    let mut middle_graph = middle.graph();
    relabel_nodes(vec![&mut left_graph, &mut middle_graph]);
    // Build combined graph
    let graph = merge_graphs(vec![&left_graph, &middle_graph]);
    let previous_credits = credit_inv.credits(left) + credit_inv.credits(middle);

    // Enumerate all possible matchings (adversarial)
    for left_matched in left_graph.nodes().powerset().filter(|p| p.len() == 3) {
        for middle_left_matched in middle_graph.nodes().powerset().filter(|p| p.len() == 3) {
            for middle_left_perm in middle_left_matched.into_iter().permutations(3) {
                // Compute edges of matching
                let left_matching: EdgeList = left_matched
                    .iter()
                    .zip(middle_left_perm.into_iter())
                    .map(|(&l, r)| (l, r, EdgeType::Zero))
                    .collect();

                
                let proved = find_local_merge_with_matching(
                    &graph,
                    &left_matching,
                    credit_inv.clone(),
                    previous_credits,
                );

                if !proved {
                    print!("   Proof with two components unsuccessful for matching {{");
                    print_matching(&left_matching, &vec![left_graph.clone(), middle_graph.clone()]);
                    println!("}}. Using three components now!");
                    for right in comps {
                        let mut right_graph = right.graph();
                        // preserves labels of middle and left
                        relabel_nodes(vec![&mut left_graph.clone(), &mut middle_graph.clone(), &mut right_graph]);
                        let graph = merge_graphs(vec![&left_graph, &middle_graph, &right_graph]);
                        let previous_credits = credit_inv.credits(left) + credit_inv.credits(middle) + credit_inv.credits(right);

                        for right_matched in right_graph.nodes().powerset().filter(|p| p.len() == 3) {
                            for middle_right_matched in middle_graph.nodes().powerset().filter(|p| p.len() == 3) {
                                for middle_right_perm in middle_right_matched.into_iter().permutations(3) {
                                    let mut right_matching: EdgeList = right_matched
                                    .iter()
                                    .zip(middle_right_perm.into_iter())
                                    .map(|(&l, r)| (l, r, EdgeType::Zero))
                                    .collect();

                                    right_matching.append(&mut left_matching.clone());

                                    let prove_simple_merge = find_local_merge_with_matching(
                                        &graph,
                                        &right_matching,
                                        credit_inv.clone(),
                                        previous_credits,
                                    );

                                    if !prove_simple_merge {
                                        return false
                                    }
                                }
                            }
                        }
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
    matching: &EdgeList,
    credit_inv: C,
    previous_credits: Rational64,
) -> bool {
    let m = graph.edge_count();
    let n = graph.node_count();

    let num_matching = matching.len();
    let sellable = edges_of_type(graph, EdgeType::One);

    enumerate_and_check(
        graph,
        matching.into_iter().cloned().powerset().filter(|p| p.len() >= 2),
        sellable
            .into_iter()
            .powerset()
            .filter(|p| m + num_matching - p.len() >= n - 1),
        credit_inv,
        previous_credits,
    )
}