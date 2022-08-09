use std::fmt::Display;

use num_rational::Rational64;

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum EdgeType {
    // Not sellable
    Fixed,
    // sellable
    One,
    // buyable
    Zero,
}

pub type Graph = petgraph::graphmap::UnGraphMap<u32, EdgeType>;
pub type EdgeList = Vec<(u32, u32, EdgeType)>;

pub fn three_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 0, EdgeType::One),
    ]))
}

pub fn four_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 3, EdgeType::One),
        (3, 0, EdgeType::One),
    ]))
}

pub fn five_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 3, EdgeType::One),
        (3, 4, EdgeType::One),
        (4, 0, EdgeType::One),
    ]))
}
pub fn six_cycle() -> Component {
    Component::Simple(Graph::from_edges(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 3, EdgeType::One),
        (3, 4, EdgeType::One),
        (4, 5, EdgeType::One),
        (5, 0, EdgeType::One),
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
