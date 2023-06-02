use crate::{comps::Component, EdgeType, Graph, Node};

use itertools::{iproduct, Itertools};

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

#[allow(dead_code)]
pub fn get_local_merge_graph(
    comp1: &Component,
    comp2: &Component,
    matching: &Vec<(Node, Node)>,
) -> Graph {
    let mut graph = comp1.graph();
    for (v1, v2, t) in comp2.graph().all_edges() {
        graph.add_edge(v1, v2, *t);
    }
    for (m1, m2) in matching {
        graph.add_edge(*m1, *m2, EdgeType::Buyable);
    }
    graph
}

pub fn product_of_first<T: Clone + Copy + 'static>(
    mut edges: Vec<Vec<T>>,
) -> Box<dyn Iterator<Item = Vec<T>>> {
    let length = edges.len();
    if length == 9 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);
        let edges5 = edges.remove(0);
        let edges6 = edges.remove(0);
        let edges7 = edges.remove(0);
        let edges8 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4, edges5, edges6, edges7, edges8)
                .map(|(e1, e2, e3, e4, e5, e6, e7, e8, e9)| vec![e1, e2, e3, e4, e5, e6, e7, e8, e9]),
        )
    } else if length == 8 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);
        let edges5 = edges.remove(0);
        let edges6 = edges.remove(0);
        let edges7 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4, edges5, edges6, edges7)
                .map(|(e1, e2, e3, e4, e5, e6, e7, e8)| vec![e1, e2, e3, e4, e5, e6, e7, e8]),
        )
    } else if length == 7 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);
        let edges5 = edges.remove(0);
        let edges6 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4, edges5, edges6)
                .map(|(e1, e2, e3, e4, e5, e6, e7)| vec![e1, e2, e3, e4, e5, e6, e7]),
        )
    } else if length == 6 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);
        let edges5 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4, edges5)
                .map(|(e1, e2, e3, e4, e5, e6)| vec![e1, e2, e3, e4, e5, e6]),
        )
    } else if length == 5 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4)
                .map(|(e1, e2, e3, e4, e5)| vec![e1, e2, e3, e4, e5]),
        )
    } else if length == 4 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3).map(|(e1, e2, e3, e4)| vec![e1, e2, e3, e4]),
        )
    } else if length == 3 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);

        Box::new(iproduct!(edges0, edges1, edges2).map(|(e1, e2, e3)| vec![e1, e2, e3]))
    } else if length == 2 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);

        Box::new(iproduct!(edges0, edges1).map(|(e1, e2)| vec![e1, e2]))
    } else if length == 1 {
        let edges0 = edges.remove(0);

        Box::new(iproduct!(edges0).map(|e1| vec![e1]))
    } else {
        panic!("Pseudo Cycle Enumeration: length {} not supported!", length)
    }
}

pub fn relabels_nodes_sequentially(comps: &mut [Component], mut offset: u32) {
    for comp in comps {
        match comp {
            Component::C7(nodes) => offset += relabel_slice(nodes, offset),
            Component::C6(nodes) => offset += relabel_slice(nodes, offset),
            Component::C5(nodes) => offset += relabel_slice(nodes, offset),
            Component::C4(nodes) => offset += relabel_slice(nodes, offset),
            Component::C3(nodes) => offset += relabel_slice(nodes, offset),
            Component::Large(n) => {
                n.set_id(offset);
                offset += 1;
            } // Component::ComplexPath(c, blacks) => {
              //     c.graph = Graph::from_edges(c.graph.all_edges().map(|(mut w1, mut w2, t)| {
              //         w1.inc_id(offset);
              //         w2.inc_id(offset);
              //         (w1, w2, *t)
              //     }));
              //     blacks.iter_mut().for_each(|n| n.inc_id(offset));
              //     offset += c.graph.node_count() as u32;
              // }
              // Component::ComplexTree(c, blacks) => {
              //     c.graph = Graph::from_edges(c.graph.all_edges().map(|(mut w1, mut w2, t)| {
              //         w1.inc_id(offset);
              //         w2.inc_id(offset);
              //         (w1, w2, *t)
              //     }));
              //     blacks.iter_mut().for_each(|n| n.inc_id(offset));
              //     offset += c.graph.node_count() as u32;
              // }
        }
    }
}

fn relabel_slice(slice: &mut [Node], offset: u32) -> u32 {
    slice.iter_mut().for_each(|n| n.inc_id(offset));
    slice.len() as u32
}
