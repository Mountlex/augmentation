use std::fmt::Display;

use num_rational::Rational64;

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
    Component::Large
}

#[derive(Clone, Debug)]
pub enum Component {
    Simple(Graph),
    Large,
}

impl Component {
    pub fn graph(&self) -> Graph {
        match self {
            Component::Large => Graph::from_edges(vec![
                (0, 1, EdgeType::Fixed),
                (1, 2, EdgeType::Fixed),
                (0, 2, EdgeType::Fixed),
            ]),
            Component::Simple(list) => list.clone(),
        }
    }
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Large => write!(f, "Large"),
            Component::Simple(graph) => write!(f, "{}-Cycle", graph.node_count()),
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
pub fn merge_to_base(mut base: Graph, others: Vec<&Graph>) -> (Graph, Vec<Vec<Node>>) {
    let mut offset: u32 = base.nodes().max().unwrap() + 1;
    let mut indices = vec![];
    for graph in others {
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
        base.extend(edges);
        indices.push((offset..(offset + nodes.len() as u32)).collect::<Vec<Node>>());
        offset += nodes.len() as u32;
    }

    (base, indices)
}

pub fn edges_of_type<'a>(graph: &'a Graph, typ: EdgeType) -> Vec<(Node, Node)> {
    graph
        .all_edges()
        .filter(|(_, _, t)| **t == typ)
        .map(|(a, b, _)| (a, b))
        .collect()
}

pub fn merge(graphs: Vec<&Graph>) -> (Graph, Vec<Vec<Node>>) {
    let mut offset: u32 = 0;
    let mut indices = vec![];
    let mut base = Graph::new();
    for graph in graphs {
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
        base.extend(edges);
        indices.push((offset..(offset + nodes.len() as u32)).collect::<Vec<Node>>());
        offset += nodes.len() as u32;
    }

    (base, indices)
}

pub trait CreditInvariant: Clone {
    fn credits(&self, comp: &Component) -> Rational64;
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
    fn credits(&self, comp: &Component) -> Rational64 {
        match comp {
            Component::Large => Rational64::from_integer(2),
            Component::Simple(graph) => {
                self.c * Rational64::from_integer(graph.edge_count() as i64)
            }
        }
    }
}


#[cfg(test)]
mod test_merge {
    use super::*;

    #[test]
    fn test_two_triangles() {
        let base = three_cycle().graph();
        let other = three_cycle().graph();
        let (base, nodes) = merge_to_base(base, vec![&other]);

        assert_eq!(base.node_count(), 6);
        assert_eq!(nodes[0], vec![3, 4, 5])
    }

    #[test]
    fn test_three_triangles() {
        let base = three_cycle().graph();
        let other1 = three_cycle().graph();
        let other2 = three_cycle().graph();
        let (base, nodes) = merge_to_base(base, vec![&other1, &other2]);

        assert_eq!(base.node_count(), 9);
        assert_eq!(nodes[0], vec![3, 4, 5]);
        assert_eq!(nodes[1], vec![6, 7, 8]);
    }
}
