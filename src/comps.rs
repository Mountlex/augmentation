use std::fmt::Display;

use itertools::Itertools;

use crate::{Credit, CreditInv, Graph, Node};

use super::types::Edge;

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum EdgeType {
    // Not sellable
    Fixed,
    // sellable
    Sellable,
    // buyable
    Buyable,
}

pub fn c4() -> Component {
    Component::C4([0.into(), 1.into(), 2.into(), 3.into()])
}
pub fn c5() -> Component {
    Component::C5([0.into(), 1.into(), 2.into(), 3.into(), 4.into()])
}
pub fn c6() -> Component {
    Component::C6([0.into(), 1.into(), 2.into(), 3.into(), 4.into(), 5.into()])
}
pub fn c7() -> Component {
    Component::C7([
        0.into(),
        1.into(),
        2.into(),
        3.into(),
        4.into(),
        5.into(),
        6.into(),
    ])
}
pub fn large() -> Component {
    Component::Large(Node::Comp(0))
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompType {
    Cycle(usize),
    Large,
}

impl Display for CompType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompType::Cycle(i) => write!(f, "C{}", i),
            CompType::Large => write!(f, "Lrg"),
        }
    }
}

#[derive(Clone, Debug)]
pub enum Component {
    C7([Node; 7]),
    C6([Node; 6]),
    C5([Node; 5]),
    C4([Node; 4]),
    C3([Node; 3]),
    Large(Node),
}

impl Component {
    pub fn is_cycle(&self) -> bool {
        self.is_c3() || self.is_c4() || self.is_c5() || self.is_c6() || self.is_c7()
    }

    pub fn is_c7(&self) -> bool {
        matches!(self, Component::C7(_))
    }
    pub fn is_c6(&self) -> bool {
        matches!(self, Component::C6(_))
    }

    pub fn is_c5(&self) -> bool {
        matches!(self, Component::C5(_))
    }

    pub fn is_c4(&self) -> bool {
        matches!(self, Component::C4(_))
    }

    pub fn is_c3(&self) -> bool {
        matches!(self, Component::C3(_))
    }

    pub fn paths_between(&self, v: &Node, u: &Node) -> (Vec<Node>, Vec<Node>) {
        let nodes = self.nodes().to_owned();

        let mut path1 = vec![*v];
        let mut iter = nodes.iter().cycle();
        while Some(v) != iter.next() {}
        for node in iter {
            path1.push(*node);
            if node == u {
                break;
            }
        }

        let mut path2 = vec![*u];
        let mut iter = nodes.iter().cycle();
        while Some(u) != iter.next() {}
        for node in iter {
            path2.push(*node);
            if node == v {
                break;
            }
        }

        (path1, path2)
    }

    pub fn symmetric_combs(&self) -> Vec<[Node; 2]> {
        match self {
            // must be consistent with the fact that fixed node is n[0]!!! see below
            Component::C7(n) => vec![[n[1], n[2]], [n[1], n[3]], [n[2], n[4]], [n[1], n[4]]],
            Component::C6(n) => vec![[n[1], n[2]], [n[1], n[3]], [n[2], n[4]]],
            Component::C5(n) => vec![[n[1], n[2]], [n[1], n[3]]],
            Component::C4(n) => vec![[n[1], n[2]]],
            Component::C3(n) => vec![[n[1], n[2]]],
            _ => panic!("Complex or large is not symmetric!"),
        }
    }

    pub fn fixed_node(&self) -> Option<Node> {
        match self {
            Component::C7(nodes) => Some(nodes[0]),
            Component::C6(nodes) => Some(nodes[0]),
            Component::C5(nodes) => Some(nodes[0]),
            Component::C4(nodes) => Some(nodes[0]),
            Component::C3(nodes) => Some(nodes[0]),
            Component::Large(node) => Some(*node),
        }
    }

    pub fn is_large(&self) -> bool {
        matches!(self, Component::Large(_))
    }

    pub fn nodes(&self) -> &[Node] {
        match self {
            Component::C7(nodes) => nodes,
            Component::C6(nodes) => nodes,
            Component::C5(nodes) => nodes,
            Component::C4(nodes) => nodes,
            Component::C3(nodes) => nodes,
            Component::Large(_) => panic!("large has no known nodes"),
        }
    }

    pub fn matching_nodes(&self) -> &[Node] {
        match self {
            Component::Large(n) => std::slice::from_ref(n),
            _ => self.nodes(),
        }
    }

    /// A list of all nodes which could be in-nodes.
    /// Removes symmetric cases.
    pub fn in_nodes(&self) -> &[Node] {
        match self {
            Component::Large(n) => std::slice::from_ref(n),
            _ => &self.nodes() [..(self.nodes().len() / 2 + 1)],
        }
    }

    pub fn incident(&self, edge: &Edge) -> Option<Node> {
        if let Component::Large(n) = self {
            if edge.node_incident(n) {
                Some(*n)
            } else {
                None
            }
        } else {
            self.nodes().iter().find(|n| edge.node_incident(n)).cloned()
        }
    }

    pub fn edges(&self) -> Vec<(Node, Node)> {
        match self {
            Component::C7(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C6(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C5(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C4(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C3(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::Large(_nodes) => vec![],
        }
    }

    pub fn short_name(&self) -> String {
        match self {
            Component::C7(_) => "C7".to_string(),
            Component::C6(_) => "C6".to_string(),
            Component::C5(_) => "C5".to_string(),
            Component::C4(_) => "C4".to_string(),
            Component::C3(_) => "C3".to_string(),
            Component::Large(_) => "Large".to_string(),
        }
    }

    

    pub fn num_edges(&self) -> usize {
        match self {
            Component::C7(_) => 7,
            Component::C6(_) => 6,
            Component::C5(_) => 5,
            Component::C4(_) => 4,
            Component::C3(_) => 3,
            Component::Large(_) => 8,
        }
    }

    pub fn num_vertices(&self) -> usize {
        match self {
            Component::C7(_) => 7,
            Component::C6(_) => 6,
            Component::C5(_) => 5,
            Component::C4(_) => 4,
            Component::C3(_) => 3,
            Component::Large(_) => 8,
        }
    }

    pub fn is_adjacent(&self, v1: &Node, v2: &Node) -> bool {
        //assert!(self.graph().contains_node(v1));
        //assert!(self.graph().contains_node(v2));
        match self {
            Component::C7(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C6(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C5(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C4(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C3(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::Large(_) => false,
        }
    }

    pub fn white_nodes(&self) -> Vec<Node> {
        match self {
            Component::Large(n) => vec![*n],
            _ => vec![],
        }
    }

    pub fn graph(&self) -> Graph {
        match self {
            Component::C7(_)
            | Component::C6(_)
            | Component::C5(_)
            | Component::C4(_)
            | Component::C3(_) => Graph::from_edges(
                self.edges()
                    .into_iter()
                    .map(|(u, v)| (u, v, EdgeType::Sellable))
                    .collect_vec(),
            ),
            Component::Large(n) => {
                let mut g = Graph::new();
                g.add_node(*n);
                g
            }
        }
    }

    pub fn comp_type(&self) -> CompType {
        match self {
            Component::C7(nodes) => CompType::Cycle(nodes.len()),
            Component::C6(nodes) => CompType::Cycle(nodes.len()),
            Component::C5(nodes) => CompType::Cycle(nodes.len()),
            Component::C4(nodes) => CompType::Cycle(nodes.len()),
            Component::C3(nodes) => CompType::Cycle(nodes.len()),
            Component::Large(_) => CompType::Large,
        }
    }

    pub fn combinations_with_replacement(&self, size: usize) -> Vec<Vec<Node>> {
        match self {
            Component::Large(n) => vec![vec![*n; size]],
            _ => self
                .nodes()
                .to_vec()
                .into_iter()
                .combinations_with_replacement(size)
                .collect(),
        }
    }

    pub fn contains(&self, node: &Node) -> bool {
        if let Component::Large(n) = self {
            n == node
        } else {
            self.nodes().contains(node)
        }
    }

    pub fn num_labels(&self) -> usize {
        match self {
            Component::C7(_) => 7,
            Component::C6(_) => 6,
            Component::C5(_) => 5,
            Component::C4(_) => 4,
            Component::C3(_) => 3,
            Component::Large(_) => 1,
        }
    }
}

fn is_adjacent_in_cycle(nodes: &[Node], v1: &Node, v2: &Node) -> bool {
    if !nodes.contains(v1) || !nodes.contains(v2) || v1.is_comp() || v2.is_comp() {
        return false;
    }
    // Assumes that nodes are numbered sequentially from nodes[0],...,nodes[k]

    v1.to_vertex().max(v2.to_vertex()) - v1.to_vertex().min(v2.to_vertex()) == 1
        || (nodes.first() == Some(v1) && nodes.last() == Some(v2))
        || (nodes.first() == Some(v2) && nodes.last() == Some(v1))
}

fn nodes_to_edges(nodes: &[Node]) -> Vec<(Node, Node)> {
    vec![nodes, &[nodes[0]]]
        .concat()
        .windows(2)
        .map(|w| (w[0], w[1]))
        .collect_vec()
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::C7(nodes) => write!(f, "C7 [{}]", nodes.iter().join("-")),
            Component::C6(nodes) => write!(f, "C6 [{}]", nodes.iter().join("-")),
            Component::C5(nodes) => write!(f, "C5 [{}]", nodes.iter().join("-")),
            Component::C4(nodes) => write!(f, "C4 [{}]", nodes.iter().join("-")),
            Component::C3(nodes) => write!(f, "C3 [{}]", nodes.iter().join("-")),
            Component::Large(n) => write!(f, "Large [{}]", n),
        }
    }
}

// #[derive(Clone, Debug)]
// pub struct Complex {
//     pub graph: Graph,
//     pub total_black_deg: usize,
//     pub num_blocks: usize,
// }

// pub fn edges_of_type(graph: &Graph, typ: EdgeType) -> Vec<(Node, Node)> {
//     graph
//         .all_edges()
//         .filter(|(_, _, t)| **t == typ)
//         .map(|(a, b, _)| (a, b))
//         .collect()
// }

impl CreditInv {
    pub fn credits(&self, comp: &Component) -> Credit {
        match comp {
            Component::C7(_) => self.two_ec_credit(7),
            Component::C6(_) => self.two_ec_credit(6),
            Component::C5(_) => self.two_ec_credit(5),
            Component::C4(_) => self.two_ec_credit(4),
            Component::C3(_) => self.two_ec_credit(3),
            Component::Large(_) => self.large(),
        }
    }
}
