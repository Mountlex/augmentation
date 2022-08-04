use std::fmt::Display;

use num_rational::Rational64;

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum EdgeType {
    Fixed,
    One,
    Zero,
}

pub type Graph = petgraph::graphmap::UnGraphMap<u32, EdgeType>;
pub type EdgeList = Vec<(u32, u32, EdgeType)>;

pub fn three_cycle() -> Component {
    Component::Simple(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 0, EdgeType::One),
    ])
}

pub fn four_cycle() -> Component {
    Component::Simple(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 3, EdgeType::One),
        (3, 0, EdgeType::One),
    ])
}

pub fn five_cycle() -> Component {
    Component::Simple(vec![
        (0, 1, EdgeType::One),
        (1, 2, EdgeType::One),
        (2, 3, EdgeType::One),
        (3, 4, EdgeType::One),
        (4, 0, EdgeType::One),
    ])
}

pub fn large_component() -> Component {
    Component::Large
}

#[derive(Clone, Debug)]
pub enum Component {
    Simple(EdgeList),
    Large,
}

impl Component {
    pub fn edge_list(&self) -> EdgeList {
        match self {
            Component::Large => vec![
                (0, 1, EdgeType::Fixed),
                (1, 2, EdgeType::Fixed),
                (0, 2, EdgeType::Fixed),
            ],
            Component::Simple(list) => list.clone(),
        }
    }

    
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Large => write!(f, "Large"),
            Component::Simple(list) => write!(f, "{}-Cycle", list.len()),
        }
    }
}


pub trait CreditInvariant: Clone {
    fn credits(&self, comp: &Component) -> Rational64;
}

#[derive(Clone, Debug)]
pub struct DefaultCredits {
    c: Rational64,
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
            Component::Simple(list) => self.c * Rational64::from_integer(list.len() as i64),
        }
    }
}
