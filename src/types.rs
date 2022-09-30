use std::fmt::Display;

use crate::comps::Node;

#[derive(Copy, Clone, Debug, Default)]
pub struct Edge(pub Node, pub Node);

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        (self.0 == other.0 && self.1 == other.1) || (self.0 == other.1 && self.1 == other.0)
    }
}

impl Edge {
    pub fn nodes_incident(&self, nodes: &[Node]) -> bool {
        nodes.contains(&self.0) || nodes.contains(&self.1)
    }
    pub fn node_incident(&self, n: &Node) -> bool {
        n == &self.0 || n == &self.1
    }
    pub fn edge_incident(&self, edge: &Edge) -> bool {
        self.0 == edge.0 || self.1 == edge.0 || self.0 == edge.1 || self.1 == edge.1
    }

    pub fn reverse(&self) -> Edge {
        Edge(self.1, self.0)
    }
}

impl Eq for Edge {}

impl Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.0, self.1)
    }
}
