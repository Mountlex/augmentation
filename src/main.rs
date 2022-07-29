use std::fmt::Display;

use itertools::Itertools;
use petgraph::algo::connected_components;
use petgraph::dot::{Config, Dot};

use crate::bridges::has_bridges;

mod bridges;

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
enum EdgeType {
    Fixed,
    One,
    Zero,
}

type Graph = petgraph::graphmap::UnGraphMap<u32, EdgeType>;
type EdgeList = Vec<(u32, u32, EdgeType)>;

fn three_cycle() -> Component {
    Component::Simple(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 0, EdgeType::One),
    ])
}

fn four_cycle() -> Component {
    Component::Simple(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 3, EdgeType::One),
        (3, 0, EdgeType::One),
    ])
}

fn five_cycle() -> Component {
    Component::Simple(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 3, EdgeType::One),
        (3, 4, EdgeType::One),
        (4, 0, EdgeType::One),
    ])
}

fn fixed_component() -> Component {
    Component::Large(vec![
        (0, 1, EdgeType::Fixed),
        (1, 2, EdgeType::Fixed),
        (0, 2, EdgeType::Fixed),
    ])
}

#[derive(Clone, Debug)]
enum Component {
    Simple(EdgeList),
    Large(EdgeList),
}

impl Component {
    fn edge_list<'a>(&'a self) -> &'a EdgeList {
        match self {
            Component::Large(list) => list,
            Component::Simple(list) => list,
        }
    }

    fn credits(&self) -> f32 {
        match self {
            Component::Large(_) => 2.0,
            Component::Simple(list) => list.len() as f32 * 0.34,
        }
    }
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Large(_) => write!(f, "Large"),
            Component::Simple(list) => write!(f, "{}-Cycle", list.len()),
        }
    }
}

fn main() {
    let graphs = vec![three_cycle(), four_cycle(), five_cycle(), fixed_component()];

    // Enumerate every graph combination
    for left in graphs.clone() {
        let left_edges = left.edge_list().clone();
        let n_left = Graph::from_edges(&left_edges).node_count() as u32;
        for right in graphs.clone() {
            let mut right_edges = right.edge_list().clone();
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
                        let credits = left.credits() + right.credits();
                        test_graph(graph, matching, credits);
                    }
                }
            }

            // If we found shortcuts for every matching, this combination is valid
            println!("Checked  {} and {}!", left, right);
        }
    }
}

fn test_graph(graph: Graph, matching: EdgeList, credits: f32) {
    let shortcutable: Vec<(u32, u32, &EdgeType)> = graph
        .all_edges()
        .filter(|(_, _, t)| **t == EdgeType::One)
        .collect();

    for buy in matching.iter().powerset().filter(|p| p.len() >= 2) {
        for shortcut in shortcutable.iter().powerset() {
            let s = shortcut.len();
            let b = buy.len();
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
                if credits - b as f32 + s as f32 >= 2.0 {
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
