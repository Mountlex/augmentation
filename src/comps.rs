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
    Component::C3([0.into(), 1.into(), 2.into()])
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

pub fn complex_path() -> Component {
    Component::ComplexPath(
        Complex {
            ///
            /// 0 -- 1 -- 2 -- 3 -- 4 -- 5 -- 6
            ///
            graph: Graph::from_edges(vec![
                (Node::c(0), 1.into(), EdgeType::Fixed),
                (1.into(), 2.into(), EdgeType::Sellable),
                (2.into(), 3.into(), EdgeType::Sellable),
                (3.into(), 4.into(), EdgeType::Sellable),
                (4.into(), 5.into(), EdgeType::Sellable),
                (5.into(), Node::c(6), EdgeType::Fixed),
            ]),
            num_blocks: 2,
            total_black_deg: 10,
        },
        [1.into(), 2.into(), 3.into(), 4.into(), 5.into()],
    )
}

pub fn complex_tree() -> Component {
    Component::ComplexTree(
        Complex {
            ///          0
            ///          |
            ///          1
            ///          |
            ///          2 -- 5 -- 6
            ///          |
            ///          3
            ///          |
            ///          4
            graph: Graph::from_edges(vec![
                (Node::c(0), 1.into(), EdgeType::Fixed),
                (1.into(), 2.into(), EdgeType::Sellable),
                (2.into(), 3.into(), EdgeType::Sellable),
                (3.into(), Node::c(4), EdgeType::Fixed),
                (2.into(), 5.into(), EdgeType::Sellable),
                (5.into(), Node::c(6), EdgeType::Fixed),
            ]),
            num_blocks: 3,
            total_black_deg: 9,
        },
        [1.into(), 2.into(), 3.into(), 5.into()],
    )
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CompType {
    Cycle(usize),
    Large,
    Complex,
}

impl Display for CompType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CompType::Cycle(i) => write!(f, "C{}", i),
            CompType::Large => write!(f, "Lrg"),
            CompType::Complex => write!(f, "Cpx"),
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
    ComplexPath(Complex, [Node; 5]),
    ComplexTree(Complex, [Node; 4]),
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

        let mut path1 = vec![v.clone()];
        let mut iter = nodes.iter().cycle();
        while Some(v) != iter.next() {}
        while let Some(node) = iter.next() {
            path1.push(*node);
            if node == u {
                break;
            }
        }

        let mut path2 = vec![u.clone()];
        let mut iter = nodes.iter().cycle();
        while Some(u) != iter.next() {}
        while let Some(node) = iter.next() {
            path2.push(*node);
            if node == v {
                break;
            }
        }

        (path1, path2)
    }

    pub fn symmetric_combs(&self) -> Vec<[Node; 2]> {
        match self {
            // must be consistent with the fact that fixed node is n[0]!!!
            Component::C7(n) => vec![[n[1], n[2]], [n[1], n[3]], [n[2], n[4]], [n[1], n[4]]],
            Component::C6(n) => vec![[n[1], n[2]], [n[1], n[3]], [n[2], n[4]]],
            Component::C5(n) => vec![[n[1], n[2]], [n[1], n[3]]],
            Component::C4(n) => vec![[n[1], n[2]]],
            Component::C3(n) => vec![[n[1], n[2]]],
            _ => panic!("Complex or large is not symmetric!"),
        }
    }

    pub fn is_complex(&self) -> bool {
        matches!(self, Component::ComplexPath(_, _)) || matches!(self, Component::ComplexTree(_, _))
    }

    pub fn is_large(&self) -> bool {
        matches!(self, Component::Large(_))
    }

    pub fn complex_degree_between(&self, u: &Node, v: &Node) -> u32 {
        match self {
            Component::ComplexPath(_, _) => {
                (u.to_vertex().max(v.to_vertex()) - u.to_vertex().min(v.to_vertex()) + 1) * 2
            }
            Component::ComplexTree(_, b) => {
                if b[..3].contains(u) && b[..3].contains(v) {
                    (u.to_vertex().max(v.to_vertex()) - u.to_vertex().min(v.to_vertex()) + 1) * 2
                        + if u.to_vertex().min(v.to_vertex()) <= b[1].to_vertex()
                            && u.to_vertex().max(v.to_vertex()) >= b[1].to_vertex()
                        {
                            1
                        } else {
                            0
                        }
                } else if b[3..].contains(u) && b[3..].contains(v) {
                    (u.to_vertex().max(v.to_vertex()) - u.to_vertex().min(v.to_vertex()) + 1) * 2
                } else {
                    if b[3..].contains(v) {
                        (u.to_vertex().max(b[1].to_vertex()) - u.to_vertex().min(b[1].to_vertex())
                            + v.to_vertex().max(b[1].to_vertex())
                            - v.to_vertex().min(b[1].to_vertex())
                            - 2
                            + 1)
                            * 2
                            + 1
                    } else {
                        (v.to_vertex().max(b[1].to_vertex()) - v.to_vertex().min(b[1].to_vertex())
                            + u.to_vertex().max(b[1].to_vertex())
                            - u.to_vertex().min(b[1].to_vertex())
                            - 2
                            + 1)
                            * 2
                            + 1
                    }
                }
            }
            _ => panic!("Component is not complex!"),
        }
    }

    pub fn nodes(&self) -> &[Node] {
        match self {
            Component::C7(nodes) => nodes,
            Component::C6(nodes) => nodes,
            Component::C5(nodes) => nodes,
            Component::C4(nodes) => nodes,
            Component::C3(nodes) => nodes,
            Component::Large(_) => panic!("large has no known nodes"),
            Component::ComplexPath(_, nodes) => nodes,
            Component::ComplexTree(_, nodes) => nodes,
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

    pub fn sym_matching_nodes(&self) -> &[Node] {
        match self {
            Component::Large(n) => std::slice::from_ref(n),
            Component::ComplexTree(_, nodes) => nodes,
            Component::ComplexPath(_, nodes) => nodes,
            _ => &self.nodes()[..(self.nodes().len() / 2 + 1)],
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
            Component::C7(_) => format!("C7"),
            Component::C6(_) => format!("C6"),
            Component::C5(_) => format!("C5"),
            Component::C4(_) => format!("C4"),
            Component::C3(_) => format!("C3"),
            Component::Large(_) => format!("Large"),
            Component::ComplexPath(_, _) => format!("Complex-Path"),
            Component::ComplexTree(_, _) => format!("Complex-Tree"),
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
            Component::ComplexPath(_, _) => None,
            Component::ComplexTree(_, _) => None,
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
            Component::ComplexPath(_, _) => 8,
            Component::ComplexTree(_, _) => 8,
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
            Component::ComplexPath(complex, _) => complex.graph.neighbors(*v1).contains(&v2),
            Component::ComplexTree(complex, _) => complex.graph.neighbors(*v1).contains(&v2),
        }
    }

    pub fn white_nodes(&self) -> Vec<Node> {
        match self {
            Component::Large(n) => vec![*n],
            Component::ComplexPath(complex, _) | Component::ComplexTree(complex, _) => complex
                .graph
                .nodes()
                .filter(|n| matches!(n, Node::Comp(_)))
                .collect_vec(),
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
            Component::ComplexPath(c, _) => c.graph.clone(),
            Component::ComplexTree(c, _) => c.graph.clone(),
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
            Component::ComplexPath(_, _) => 7,
            Component::ComplexTree(_, _) => 7,
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
            Component::C7(nodes) => write!(f, "C7 [{}]", nodes.into_iter().join("-")),
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
            Component::C7(_) => self.two_ec_credit(7),
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

#[cfg(test)]
mod test_complex_degree {
    use super::*;

    #[test]
    fn test_complex_path() {
        let comp = complex_path();

        assert_eq!(comp.complex_degree_between(&Node::n(1), &Node::n(4)), 8);
        assert_eq!(comp.complex_degree_between(&Node::n(1), &Node::n(2)), 4);
        assert_eq!(comp.complex_degree_between(&Node::n(1), &Node::n(1)), 2);
    }

    #[test]
    fn test_complex_tree() {
        let comp = complex_tree();
        //          0
        //          |
        //          1
        //          |
        //          2 -- 5 -- 6
        //          |
        //          3
        //          |
        //          4
        assert_eq!(comp.complex_degree_between(&Node::n(1), &Node::n(3)), 7);
        assert_eq!(comp.complex_degree_between(&Node::n(1), &Node::n(2)), 5);
        assert_eq!(comp.complex_degree_between(&Node::n(1), &Node::n(5)), 7);
        assert_eq!(comp.complex_degree_between(&Node::n(2), &Node::n(2)), 3);
        assert_eq!(comp.complex_degree_between(&Node::n(3), &Node::n(3)), 2);
        assert_eq!(comp.complex_degree_between(&Node::n(3), &Node::n(5)), 7);
        assert_eq!(comp.complex_degree_between(&Node::n(2), &Node::n(2)), 3);
    }
}
