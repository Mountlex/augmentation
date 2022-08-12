use std::fmt::Display;

use itertools::Itertools;
use num_rational::Rational64;

use crate::Credit;

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum EdgeType {
    // Not sellable
    Fixed,
    // sellable
    Sellable,
    // buyable
    Buyable,
}

pub type Node = u32;
pub type Graph = petgraph::graphmap::UnGraphMap<Node, EdgeType>;

pub fn three_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 0, EdgeType::Sellable),
    ]))
}

pub fn four_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 0, EdgeType::Sellable),
    ]))
}

pub fn five_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 4, EdgeType::Sellable),
        (4, 0, EdgeType::Sellable),
    ]))
}
pub fn six_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 4, EdgeType::Sellable),
        (4, 5, EdgeType::Sellable),
        (5, 0, EdgeType::Sellable),
    ]))
}

pub fn large_component() -> Component {
    Component::Large(Graph::from_edges(vec![
        (0, 1, EdgeType::Fixed),
        (1, 2, EdgeType::Fixed),
        (0, 2, EdgeType::Fixed),
    ]))
}

pub fn complex_component() -> Component {
    Component::Complex(Graph::from_edges(vec![
        (0, 1, EdgeType::Fixed),
        (1, 2, EdgeType::Fixed),
        (0, 2, EdgeType::Fixed),
    ]))
}

#[derive(Clone, Debug)]
pub enum Component {
    Simple(Graph),
    Large(Graph),
    Complex(Graph),
}

impl Component {
    pub fn short_name(&self) -> String {
        match self {
            Component::Large(_) => format!("large"),
            Component::Complex(_) => format!("complex"),
            Component::Simple(graph) => format!("{}c", graph.node_count()),
        }
    }

    pub fn graph(&self) -> &Graph {
        match self {
            Component::Simple(g) => g,
            Component::Large(g) => g,
            Component::Complex(g) => g,
        }
    }

    pub fn graph_mut(&mut self) -> &mut Graph {
        match self {
            Component::Simple(g) => g,
            Component::Large(g) => g,
            Component::Complex(g) => g,
        }
    }

    pub fn to_graph(self) -> Graph {
        match self {
            Component::Simple(g) => g,
            Component::Large(g) => g,
            Component::Complex(g) => g,
        }
    }
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Large(_) => write!(f, "Large"),
            Component::Complex(_) => write!(f, "Complex"),
            Component::Simple(graph) => write!(f, "{}-Cycle [{}]", graph.node_count(), graph.nodes().map(|n| format!("{}", n)).join("-")),
        }
    }
}

/// Adds nodes and edges from `others` to `base` and relabels and return node weights of those.
/// The node weights of `base` will not be changed!
///
/// Example:
/// 0 - 1    0 - 1
///  \ /      \ /
///   3        2
/// base      others
///
/// gives
///
/// 0 - 1    4 - 5
///  \ /      \ /
///   3        6
///       base      
///
/// and returns [[4,5,6]]
pub fn merge_graphs_to_base(mut base: Graph, mut others: Vec<Graph>) -> (Graph, Vec<Graph>) {
    let mut offset: u32 = if let Some(max) = base.nodes().max() { max + 1} else {0};
    for graph in &mut others {
        let nodes = graph.nodes().collect::<Vec<Node>>();
        let edges: Vec<(Node, Node, EdgeType)> = graph
            .all_edges()
            .map(|(w1, w2, t)| {
                (
                    (nodes.iter().position(|n| n == &w1).unwrap() as u32 + offset),
                    (nodes.iter().position(|n| n == &w2).unwrap() as u32 + offset),
                    *t,
                )
            })
            .collect();
        base.extend(&edges);
        *graph = Graph::from_edges(edges);
        offset += nodes.len() as u32;
    }

    (base, others)
}

pub fn merge_components_to_base(base: Graph, mut others: Vec<Component>) -> (Graph, Vec<Component>) {
    let graphs = others.iter().map(|c| c.graph().clone()).collect();
    let (graph, graphs) = merge_graphs_to_base(base, graphs);
    others.iter_mut().zip(graphs).for_each(|(c, g)| *c.graph_mut() = g);
    (graph, others)
}

pub fn edges_of_type<'a>(graph: &'a Graph, typ: EdgeType) -> Vec<(Node, Node)> {
    graph
        .all_edges()
        .filter(|(_, _, t)| **t == typ)
        .map(|(a, b, _)| (a, b))
        .collect()
}

pub fn merge_graphs(graphs: Vec<Graph>) -> (Graph, Vec<Graph>) {
    merge_graphs_to_base(Graph::new(), graphs)
}

pub trait CreditInvariant: Clone {
    fn credits(&self, comp: &Component) -> Credit {
        match comp {
            Component::Complex(_) => self.complex_comp() + self.complex_black(2) + self.complex_black(2), // black vertex credit!
            Component::Large(_) => self.large(),
            Component::Simple(graph) => self.simple(graph)
        }
    }
    fn simple(&self, graph: &Graph) -> Credit;
    fn complex_comp(&self) -> Credit;
    fn complex_black(&self, deg: i64) -> Credit;
    fn complex_block(&self) -> Credit;
    fn large(&self) -> Credit;
}

#[derive(Clone, Debug)]
pub struct DefaultCredits {
    pub c: Rational64,
}

impl DefaultCredits {
    pub fn new(c: Rational64) -> Self {
        DefaultCredits { c }
    }
}

impl CreditInvariant for DefaultCredits {
    fn simple(&self, graph: &Graph) -> Credit {
        self.c * Credit::from_integer(graph.edge_count() as i64)
    }

    fn complex_comp(&self) -> Credit {
        (Credit::from_integer(13) * self.c) - Credit::from_integer(2)
    }

    fn complex_black(&self, deg: i64) -> Credit {
        Credit::from_integer(deg) * self.c * Credit::new(1,2)
    }

    fn complex_block(&self) -> Credit {
        Credit::from_integer(1) 
    }

    fn large(&self) -> Credit {
        Credit::from_integer(2)
    }
}


#[cfg(test)]
mod test_merge {
    use super::*;

    #[test]
    fn test_two_triangles() {
        let base = three_cycle().to_graph();
        let other = three_cycle();
        let (base, comps) = merge_components_to_base(base, vec![other]);

        assert_eq!(base.node_count(), 6);
        assert_eq!(comps[0].graph().nodes().collect::<Vec<u32>>(), vec![3, 4, 5])
    }

    #[test]
    fn test_three_triangles() {
        let base = three_cycle().to_graph();
        let other1 = three_cycle();
        let other2 = three_cycle();
        let (base, comps) = merge_components_to_base(base, vec![other1, other2]);

        assert_eq!(base.node_count(), 9);
        assert_eq!(comps[0].graph().nodes().collect::<Vec<u32>>(), vec![3, 4, 5]);
        assert_eq!(comps[1].graph().nodes().collect::<Vec<u32>>(), vec![6, 7, 8]);
    }
}
