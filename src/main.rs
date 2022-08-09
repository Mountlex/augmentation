use clap::Parser;
use local_merge::prove_all_local_merges;
use nice_path::prove_nice_path_progress;
use num_rational::Rational64;
use petgraph::algo::connected_components;

use crate::bridges::compute_bridges;
use crate::comps::*;

mod bridges;
mod comps;
mod nice_path;
mod local_merge;
mod contract;

#[derive(Parser)]
#[clap(author, version, about, long_about = None)]
struct Cli {
    c_numer: i64,
    c_demon: i64,
}

fn main() {
    let cli = Cli::parse();
    let inv = DefaultCredits::new(Rational64::new(cli.c_numer, cli.c_demon));
    let comps = vec![three_cycle(), four_cycle(), five_cycle(), six_cycle(), large_component()];

    println!("========== Proof for c = {} ==========", inv.c);
    prove_all_local_merges(comps.clone(), inv.clone());
    prove_nice_path_progress(comps, inv);
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

pub fn edges_of_type<'a>(graph: &'a Graph, typ: EdgeType) -> Vec<(u32, u32, EdgeType)> {
    graph
        .all_edges()
        .filter(|(_, _, t)| **t == typ)
        .map(|(a, b, c)| (a, b, *c))
        .collect()
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
