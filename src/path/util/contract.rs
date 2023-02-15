use fxhash::FxHashMap;
use itertools::Itertools;

use crate::{Node, path::proof::Instance, types::Edge};





pub fn is_contractible(vertices: Vec<Node>, ham_cycle: Vec<Edge>,  instance: &Instance) -> bool {

    let outside_edges = instance.out_edges().collect_vec();
    let rem_edge = instance.rem_edges();
    let edges = instance.all_edges();

    let inner_edges = edges.iter().filter(|e| e.between_sets(&vertices, &vertices)).collect_vec();
    let mut labels = FxHashMap::<Node, u8>::default();
    let mut good_unused_edges = Vec::<&Edge>::new();
    let mut bad_unused_edges = Vec::<&Edge>::new();

    // INIT

    for node in &vertices {
        if outside_edges.contains(&node) {
            labels.insert(*node, 0);
        } else if rem_edge.iter().any(|e| e.source == *node) {
            labels.insert(*node, 0);
        } else {
            labels.insert(*node, 2);
        }
    }

    for edge in &edges {
        if edge.one_sided_nodes_incident(&vertices) {
            let node = edge.endpoint_in(&vertices).unwrap();
            decrease_label_if_possible(&mut labels, node);
        }
    }

    for edge in inner_edges {
        let (u,v) = edge.to_tuple();
        if labels.get(&u) == Some(&0) || labels.get(&v) == Some(&0) {
            bad_unused_edges.push(edge);
        } else {
            good_unused_edges.push(edge);
        }
    }

    let mut lb = 0;

    // Greedy Matching

    // first buy good edges and update edges
    while let Some(edge) = good_unused_edges.pop() {
        let (u,v) = edge.to_tuple();
        decrease_label_if_possible(&mut labels, u);
        decrease_label_if_possible(&mut labels, v);

        lb += 1;

        // update good edges
        good_unused_edges.drain_filter(|e| {
            let (u,v) = e.to_tuple();
            labels.get(&u) == Some(&0) || labels.get(&v) == Some(&0)
        }).for_each(|e| bad_unused_edges.push(e));
    }

    // now all edges are bad. Buy remaining edges
    while let Some(edge) = bad_unused_edges.pop() {
        let (u,v) = edge.to_tuple();
        if labels.get(&u).unwrap() > &0 || labels.get(&v).unwrap() > &0 {
            decrease_label_if_possible(&mut labels, u);
            decrease_label_if_possible(&mut labels, v);

            lb += 1;
        }
    }

    let alg = ham_cycle.len();
   
    return (alg as f64) / (lb as f64) <= 1.25

}

fn decrease_label_if_possible(labels: &mut FxHashMap::<Node, u8>, node: Node) {
    let label = labels.get_mut(&node).unwrap();
    if *label > 0 {
        *label = *label - 1;
    }
}