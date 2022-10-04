use std::collections::HashMap;

use itertools::Itertools;
use petgraph::visit::{depth_first_search, Control, DfsEvent};

use crate::comps::{Component, EdgeType};
use crate::{Credit, CreditInv, Graph, Node};

pub fn hamiltonian_paths(v1: Node, v2: Node, nodes: &[Node]) -> Vec<Vec<Node>> {
    assert!(nodes.contains(&v1));
    assert!(nodes.contains(&v2));

    nodes
        .iter()
        .cloned()
        .filter(|v| v != &v1 && v != &v2)
        .permutations(nodes.len() - 2)
        .map(|middle| vec![vec![v1], middle, vec![v2]].concat())
        .collect_vec()
}

pub fn get_local_merge_graph(
    comp1: &Component,
    comp2: &Component,
    matching: &Vec<(Node, Node)>,
) -> Graph {
    let mut graph = comp1.graph().clone();
    for (v1, v2, t) in comp2.graph().all_edges() {
        graph.add_edge(v1, v2, *t);
    }
    for (m1, m2) in matching {
        graph.add_edge(*m1, *m2, EdgeType::Buyable);
    }
    graph
}

pub fn complex_cycle_value_base(credit_inv: &CreditInv, graph: &Graph, a: Node, b: Node) -> Credit {
    let mut predecessor = HashMap::new();
    depth_first_search(&graph, Some(a), |event| {
        if let DfsEvent::TreeEdge(u, v) = event {
            predecessor.insert(v, u);
            if v == b {
                return Control::Break(v);
            }
        }
        Control::Continue
    });

    let mut next = b;
    let mut path = vec![next];
    while next != a {
        let pred = *predecessor.get(&next).unwrap();
        path.push(pred);
        next = pred;
    }
    path.reverse();

    path.into_iter()
        .map(|v| credit_inv.complex_black(graph.neighbors(v).count() as i64))
        .sum()
}
