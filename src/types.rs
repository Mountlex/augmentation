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
    pub fn incident(&self, nodes: &[Node]) -> bool {
        nodes.contains(&self.0) || nodes.contains(&self.1)
    }
}

impl Eq for Edge {}

impl Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.0, self.1)
    }
}
