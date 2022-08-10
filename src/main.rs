use bridges::has_at_least_one_bridge;
use clap::Parser;
use local_merge::prove_all_local_merges;

use num_rational::Rational64;




use petgraph::visit::{
    Dfs, EdgeCount, GraphRef, IntoNeighbors, IntoNodeIdentifiers, NodeCount, Visitable,
};


use crate::comps::*;

mod bridges;
mod comps;
mod contract;
mod local_merge;
mod nice_path;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Cli {
    c_numer: i64,
    c_demon: i64,
}

fn main() {
    let cli = Cli::parse();
    let inv = DefaultCredits::new(Rational64::new(cli.c_numer, cli.c_demon));
    let comps = vec![
        three_cycle(),
        four_cycle(),
        five_cycle(),
        six_cycle(),
        large_component(),
    ];

    println!("========== Proof for c = {} ==========", inv.c);
    prove_all_local_merges(comps, inv);
    //prove_nice_path_progress(comps, inv);
}

// TODO
pub fn relabel_nodes(graphs: Vec<&mut Graph>) {
    let mut offset = 0;
    for graph in graphs {
        let mut edges: Vec<(u32, u32, &EdgeType)> = graph.all_edges().collect();
        edges.iter_mut().for_each(|(w1, w2, _)| {
            *w1 += offset;
            *w2 += offset
        });
        offset += graph.nodes().max().unwrap() as u32 + 1;
        *graph = Graph::from_edges(edges);
    }
}

pub fn merge_graphs(graphs: Vec<&Graph>) -> Graph {
    Graph::from_edges(graphs.into_iter().flat_map(|g| g.all_edges()))
}

pub fn edges_of_type<'a>(graph: &'a Graph, typ: EdgeType) -> Vec<(Node,Node)> {
    graph
        .all_edges()
        .filter(|(_, _, t)| **t == typ)
        .map(|(a, b, _)| (a, b))
        .collect()
}

fn is_connected<G>(graph: G) -> bool
where
    G: GraphRef + Visitable + IntoNodeIdentifiers + IntoNeighbors + NodeCount + EdgeCount,
{
    if let Some(start) = graph.node_identifiers().next() {
        if graph.edge_count() + 1 < graph.node_count() {
            return false;
        }

        let mut count = 0;
        let mut dfs = Dfs::new(&graph, start);
        while let Some(_nx) = dfs.next(&graph) {
            count += 1;
        }
        count == graph.node_count()
    } else {
        true
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
    B: Iterator<Item = Vec<(u32, u32)>>+ Clone,
    S: Iterator<Item = Vec<(u32, u32)>> ,
{
    for sell in sell_iter {
        for buy in buy_iter.clone() {
            let buy_credits = Rational64::from_integer(buy.len() as i64);
            let sell_credits = Rational64::from_integer(sell.len() as i64);

            let mut graph_copy = graph.clone();
            for (u, v) in &sell {
                graph_copy.remove_edge(*u, *v);
            }
            for (u, v) in &buy {
                graph_copy.add_edge(*u, *v, EdgeType::One);
            }
            
            if !is_connected(&graph_copy) {
                continue;
            }

            if !has_at_least_one_bridge(&graph_copy) {
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

#[cfg(test)]
mod test_connected {
    use petgraph::prelude::UnGraph;

    use super::*;

    #[test]
    fn triangle() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0)]);
        assert!(is_connected(&g));
    }

    #[test]
    fn parallel_edges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (2, 3)]);
        assert!(!is_connected(&g));
    }

    #[test]
    fn two_triangles() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]);
        assert!(!is_connected(&g));
    }
}
