use std::fmt::Display;

use crate::Node;

#[derive(Copy, Clone, Debug)]
pub struct Edge {
    n1: Node,
    n2: Node,
    path_index_n1: usize,
    path_index_n2: usize,
}

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        (self.n1 == other.n1 && self.n2 == other.n2) || (self.n1 == other.n2 && self.n2 == other.n1)
    }
}

impl Edge {
    pub fn from_tuple(n1: Node, n2: Node) -> Self {
        Self {
            n1,
            n2,
            path_index_n1: 0,
            path_index_n2: 0,
        }
    }

    pub fn new(n1: Node, p1: usize, n2: Node, p2: usize) -> Self {
        Self {
            n1,
            n2,
            path_index_n1: p1,
            path_index_n2: p2,
        }
    }

    pub fn path_distance(&self) -> usize {
        self.path_index_n1.max(self.path_index_n2) - self.path_index_n1.min(self.path_index_n2)
    }

    pub fn path_indices(&self) -> (usize, usize) {
        (
            self.path_index_n1.min(self.path_index_n2),
            self.path_index_n1.max(self.path_index_n2),
        )
    }

    pub fn to_tuple(&self) -> (Node, Node) {
        (self.n1, self.n2)
    }

    pub fn endpoint_at(&self, path_idx: usize) -> Option<Node> {
        if self.path_index_n1 == path_idx {
            Some(self.n1)
        } else if self.path_index_n2 == path_idx {
            Some(self.n2)
        } else {
            None
        }
    }

    pub fn nodes_incident(&self, nodes: &[Node]) -> bool {
        nodes.contains(&self.n1) || nodes.contains(&self.n2)
    }
    pub fn node_incident(&self, n: &Node) -> bool {
        n == &self.n1 || n == &self.n2
    }
    pub fn path_incident(&self, path_idx: usize) -> bool {
        path_idx == self.path_index_n1 || path_idx == self.path_index_n2
    }

    pub fn between_path_nodes(&self, path_idx1: usize, path_idx2: usize) -> bool {
        self.path_incident(path_idx1) && self.path_incident(path_idx2)
    }

    pub fn edge_incident(&self, edge: &Edge) -> bool {
        self.n1 == edge.n1 || self.n2 == edge.n1 || self.n1 == edge.n2 || self.n2 == edge.n2
    }
}

impl Eq for Edge {}

impl Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "({}, {})", self.n1, self.n2)
    }
}
