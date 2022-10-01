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

pub fn c3() -> Component {
    Component::C3([0, 1, 2])
}
pub fn c4() -> Component {
    Component::C4([0, 1, 2, 3])
}
pub fn c5() -> Component {
    Component::C5([0, 1, 2, 3, 4])
}
pub fn c6() -> Component {
    Component::C6([0, 1, 2, 3, 4, 5])
}
pub fn large() -> Component {
    Component::Large(0)
}

pub fn complex_path() -> Component {
    Component::ComplexPath(
        Complex {
            graph: Graph::from_edges(vec![
                (0, 1, EdgeType::Fixed),
                (0, 8, EdgeType::Fixed),
                (8, 9, EdgeType::Fixed),
                (9, 0, EdgeType::Fixed),
                (1, 2, EdgeType::Sellable),
                (2, 3, EdgeType::Sellable),
                (3, 4, EdgeType::Sellable),
                (4, 5, EdgeType::Sellable),
                (5, 6, EdgeType::Sellable),
                (6, 7, EdgeType::Fixed),
                (7, 10, EdgeType::Fixed),
                (10, 11, EdgeType::Fixed),
                (11, 7, EdgeType::Fixed),
            ]),
            num_blocks: 2,
            total_black_deg: 12,
        },
        [1, 2, 3, 4, 5, 6],
    )
}

pub fn complex_tree() -> Component {
    Component::ComplexTree(
        Complex {
            ///          {0,10,11}
            ///          |
            ///          1
            ///          |
            ///          2
            ///          |
            ///          3 -- 7 -- 8 -- {9,12,13}
            ///          |
            ///          4
            ///          |
            ///          5
            ///          |
            ///          {6,14,15}
            graph: Graph::from_edges(vec![
                (0, 10, EdgeType::Fixed),
                (10, 11, EdgeType::Fixed),
                (11, 0, EdgeType::Fixed),
                (0, 1, EdgeType::Sellable),
                (1, 2, EdgeType::Sellable),
                (2, 3, EdgeType::Sellable),
                (3, 4, EdgeType::Sellable),
                (4, 5, EdgeType::Sellable),
                (3, 7, EdgeType::Sellable),
                (7, 8, EdgeType::Sellable),
                (5, 6, EdgeType::Fixed),
                (6, 14, EdgeType::Fixed),
                (14, 15, EdgeType::Fixed),
                (15, 6, EdgeType::Fixed),
                (8, 9, EdgeType::Fixed),
                (9, 12, EdgeType::Fixed),
                (12, 13, EdgeType::Fixed),
                (13, 9, EdgeType::Fixed),
            ]),
            num_blocks: 3,
            total_black_deg: 15,
        },
        [1, 2, 3, 4, 5, 7, 8],
    )
}

pub enum CompType {
    Cycle(usize),
    Large,
    Complex,
}

#[derive(Clone, Debug)]
pub enum Component {
    C6([Node; 6]),
    C5([Node; 5]),
    C4([Node; 4]),
    C3([Node; 3]),
    Large(Node),
    ComplexPath(Complex, [Node; 6]),
    ComplexTree(Complex, [Node; 7]),
}

impl Component {
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

    pub fn is_complex(&self) -> bool {
        matches!(self, Component::ComplexPath(_, _)) || matches!(self, Component::ComplexTree(_, _))
    }

    pub fn is_large(&self) -> bool {
        matches!(self, Component::Large(_))
    }

    pub fn nodes(&self) -> &[Node] {
        match self {
            Component::C6(nodes) => nodes,
            Component::C5(nodes) => nodes,
            Component::C4(nodes) => nodes,
            Component::C3(nodes) => nodes,
            Component::Large(_) => panic!("large has no known nodes"),
            Component::ComplexPath(_, nodes) => nodes,
            Component::ComplexTree(_, nodes) => nodes,
        }
    }

    pub fn possible_in_out_nodes(&self) -> &[Node] {
        match self {
            Component::C6(nodes) => nodes,
            Component::C5(nodes) => nodes,
            Component::C4(nodes) => nodes,
            Component::C3(nodes) => nodes,
            Component::Large(n) => std::slice::from_ref(n),
            Component::ComplexPath(_, nodes) => nodes,
            Component::ComplexTree(_, nodes) => nodes,
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
            Component::C6(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C5(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C4(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C3(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::Large(_nodes) => vec![],
            Component::ComplexPath(complex, _) => complex
                .graph
                .all_edges()
                .map(|(u, v, _)| (u, v))
                .collect_vec(),
            Component::ComplexTree(complex, _) => complex
                .graph
                .all_edges()
                .map(|(u, v, _)| (u, v))
                .collect_vec(),
        }
    }

    pub fn short_name(&self) -> String {
        match self {
            Component::C6(_) => format!("C6"),
            Component::C5(_) => format!("C5"),
            Component::C4(_) => format!("C4"),
            Component::C3(_) => format!("C3"),
            Component::Large(_) => format!("Large"),
            Component::ComplexPath(_, _) => format!("Complex Path"),
            Component::ComplexTree(_, _) => format!("Complex Tree"),
        }
    }

    pub fn fixed_node(&self) -> Node {
        match self {
            Component::C6(nodes) => nodes[0],
            Component::C5(nodes) => nodes[0],
            Component::C4(nodes) => nodes[0],
            Component::C3(nodes) => nodes[0],
            Component::Large(node) => *node,
            Component::ComplexPath(_, blacks) => blacks[3],
            Component::ComplexTree(_, blacks) => blacks[3],
        }
    }

    pub fn num_edges(&self) -> usize {
        match self {
            Component::C6(_) => 6,
            Component::C5(_) => 5,
            Component::C4(_) => 4,
            Component::C3(_) => 3,
            Component::Large(_) => 8,
            Component::ComplexPath(_, _) => 8,
            Component::ComplexTree(_, _) => 8,
        }
    }

    pub fn is_adjacent(&self, v1: &Node, v2: &Node) -> bool {
        //assert!(self.graph().contains_node(v1));
        //assert!(self.graph().contains_node(v2));
        match self {
            Component::C6(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C5(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C4(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C3(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::Large(_) => false,
            Component::ComplexPath(complex, _) => complex.graph.neighbors(*v1).contains(&v2),
            Component::ComplexTree(complex, _) => complex.graph.neighbors(*v1).contains(&v2),
        }
    }

    pub fn graph(&self) -> Graph {
        match self {
            Component::C6(_) | Component::C5(_) | Component::C4(_) | Component::C3(_) => {
                Graph::from_edges(
                    self.edges()
                        .into_iter()
                        .map(|(u, v)| (u, v, EdgeType::Sellable))
                        .collect_vec(),
                )
            }
            Component::Large(n) => {
                let mut g = Graph::new();
                g.add_node(*n);
                g
            }
            Component::ComplexPath(c, _) => c.graph.clone(),
            Component::ComplexTree(c, _) => c.graph.clone(),
        }
    }

    pub fn comp_type(&self) -> CompType {
        match self {
            Component::C6(nodes) => CompType::Cycle(nodes.len()),
            Component::C5(nodes) => CompType::Cycle(nodes.len()),
            Component::C4(nodes) => CompType::Cycle(nodes.len()),
            Component::C3(nodes) => CompType::Cycle(nodes.len()),
            Component::Large(_) => CompType::Large,
            Component::ComplexPath(_, _) => CompType::Complex,
            Component::ComplexTree(_, _) => CompType::Complex,
        }
    }

    pub fn matching_permutations(&self, size: usize) -> Vec<Vec<Node>> {
        match self {
            Component::Large(n) => vec![vec![*n; size]],
            Component::ComplexTree(_, nodes) => nodes.iter().cloned().permutations(size).collect(),
            Component::ComplexPath(_, nodes) => nodes.iter().cloned().permutations(size).collect(),
            _ => self
                .nodes()
                .to_vec()
                .into_iter()
                .permutations(size)
                .collect(),
        }
    }

    pub fn matching_nodes(&self) -> &[Node] {
        match self {
            Component::Large(n) => std::slice::from_ref(n),
            Component::ComplexTree(_, nodes) => nodes,
            Component::ComplexPath(_, nodes) => nodes,
            _ => self.nodes(),
        }
    }

    pub fn contains(&self, node: &Node) -> bool {
        if let Component::Large(n) = self {
            n == node
        } else {
            self.nodes().contains(node)
        }
    }
}

fn is_adjacent_in_cycle(nodes: &[Node], v1: &Node, v2: &Node) -> bool {
    // Assumes that nodes are numbered sequentially from nodes[0],...,nodes[k]

    v1.max(v2) - v1.min(v2) == 1
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
            Component::C6(nodes) => write!(f, "C6 [{}]", nodes.into_iter().join("-")),
            Component::C5(nodes) => write!(f, "C5 [{}]", nodes.into_iter().join("-")),
            Component::C4(nodes) => write!(f, "C4 [{}]", nodes.into_iter().join("-")),
            Component::C3(nodes) => write!(f, "C3 [{}]", nodes.into_iter().join("-")),
            Component::Large(n) => write!(f, "Large [{}]", n),
            Component::ComplexPath(_, _) => write!(f, "Complex Path"),
            Component::ComplexTree(_, _) => write!(f, "Complex Tree"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Complex {
    pub graph: Graph,
    pub total_black_deg: usize,
    pub num_blocks: usize,
}

pub fn edges_of_type<'a>(graph: &'a Graph, typ: EdgeType) -> Vec<(Node, Node)> {
    graph
        .all_edges()
        .filter(|(_, _, t)| **t == typ)
        .map(|(a, b, _)| (a, b))
        .collect()
}

impl CreditInv {
    pub fn credits(&self, comp: &Component) -> Credit {
        match comp {
            Component::C6(_) => self.two_ec_credit(6),
            Component::C5(_) => self.two_ec_credit(5),
            Component::C4(_) => self.two_ec_credit(4),
            Component::C3(_) => self.two_ec_credit(3),
            Component::Large(_) => self.large(),
            Component::ComplexPath(c, _) => self.complex(c),
            Component::ComplexTree(c, _) => self.complex(c),
        }
    }

    pub fn complex(&self, complex: &Complex) -> Credit {
        self.complex_comp()
            + Credit::from_integer(complex.num_blocks as i64) * self.complex_block()
            + self.complex_black(complex.total_black_deg as i64)
    }
}
