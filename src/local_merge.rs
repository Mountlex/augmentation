use std::fmt::Display;
use rayon::prelude::*;
use itertools::Itertools;
use num_rational::Rational64;

use crate::{
    comps::{Component, CreditInvariant,  EdgeType, Graph, Node},
    edges_of_type, enumerate_and_check, merge_graphs, relabel_nodes,
};

pub fn prove_all_local_merges<C: CreditInvariant + Sync>(comps: Vec<Component>, credit_inv: C) {
    // Enumerate every graph combination and prove merge
    let combinations: Vec<Vec<&Component>> = comps.iter().combinations_with_replacement(2).collect();
    combinations.par_iter().for_each(|comb| {
        let left = comb[0];
        let right = comb[1];

        println!("Local merge between {} and {}", left, right);
        if prove_local_merge(left, right, &comps, credit_inv.clone()) {
            println!("== proved ✔️")
        } else {
            println!("== disproved ❌")
        }
    });
}



#[derive(Clone, Debug)]
struct Matching<'a> {
    edges: Vec<(Node, Node)>,
    graphs: Vec<&'a Graph>
}


impl Display for Matching<'_> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (v1, v2) in &self.edges {
            let c1 = self.graphs.iter().find(|c| c.contains_node(*v1)).unwrap();
            let p1 = c1.nodes().position(|v| v == *v1).unwrap();
            let c2 = self.graphs.iter().find(|c| c.contains_node(*v2)).unwrap();
            let p2 = c2.nodes().position(|v| v == *v2).unwrap();
            write!(f, "(v{},u{}),", p1, p2)?;
        }
        write!(f,"}}")
    }
}


fn prove_local_merge_between_three<C: CreditInvariant>(
    left: &Component,
    middle: &Component,
    left_graph: Graph,
    middle_graph: Graph,
    left_matching: Matching,
    comps: &Vec<Component>,
    credit_inv: C,
) -> bool {
    for right in comps {
        println!("   Local merge between {} and {} and {}", left, middle, right);
        let mut right_graph = right.graph();
        // preserves labels of middle and left
        relabel_nodes(vec![
            &mut left_graph.clone(),
            &mut middle_graph.clone(),
            &mut right_graph,
        ]);
        let graph = merge_graphs(vec![&left_graph, &middle_graph, &right_graph]);
        let previous_credits = credit_inv.credits(left)
            + credit_inv.credits(middle)
            + credit_inv.credits(right);

        for right_matched in right_graph.nodes().powerset().filter(|p| p.len() == 3)
        {
            for middle_right_matched in
                middle_graph.nodes().powerset().filter(|p| p.len() == 3)
            {
                for middle_right_perm in
                    middle_right_matched.into_iter().permutations(3)
                {
                    let mut right_matching = Matching { edges: right_matched
                        .iter()
                        .zip(middle_right_perm.into_iter())
                        .map(|(&l, r)| (l, r))
                        .collect(),
                        graphs: vec![&left_graph,&middle_graph,&right_graph]
                    };

                    right_matching.edges.append(&mut left_matching.edges.clone());

                    let prove_simple_merge = find_local_merge_with_matching(
                        &graph,
                        &right_matching,
                        credit_inv.clone(),
                        previous_credits,
                    );

                    if !prove_simple_merge {
                        println!("   == disproved");
                        return false;
                    }
                }
            }
        }
    }
    println!("   == proved");
    true
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
                let left_matching = Matching { edges: left_matched
                    .iter()
                    .zip(middle_left_perm.into_iter())
                    .map(|(&l, r)| (l, r))
                    .collect(),
                    graphs: vec![&left_graph, &middle_graph]
                };

                let mut proved = find_local_merge_with_matching(
                    &graph,
                    &left_matching,
                    credit_inv.clone(),
                    previous_credits,
                );

                if !proved {
                    proved = prove_local_merge_between_three(left, middle, left_graph.clone(), middle_graph.clone(),left_matching.clone(), comps, credit_inv.clone());

                    if !proved {
                        proved = prove_local_merge_between_three(middle, left, middle_graph.clone(),  left_graph.clone(), left_matching, comps, credit_inv.clone());

                        if !proved {
                            return false
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
    matching: &Matching,
    credit_inv: C,
    previous_credits: Rational64,
) -> bool {
    let m = graph.edge_count();
    let n = graph.node_count();

    let num_matching = matching.edges.len();
    let sellable = edges_of_type(graph, EdgeType::One);

    let result = enumerate_and_check(
        graph,
        matching.edges
            .iter()
            .cloned()
            .powerset()
            .filter(|p| p.len() >= 2),
        sellable
            .into_iter()
            .powerset()
            .filter(|p| m + num_matching - p.len() >= n - 1),
        credit_inv,
        previous_credits,
    );

    if !result {
        println!("   Couldn't find local merge with matching edges {}", matching);
    }

    result
}
