use std::fmt::Display;

use crate::{path::Pidx, Credit, Node};

#[derive(Copy, Clone, Debug)]
pub struct Edge {
    pub n1: Node,
    pub n2: Node,
    pub path_index_n1: Pidx,
    pub path_index_n2: Pidx,
    pub cost: Credit,
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
            path_index_n1: Pidx::Last,
            path_index_n2: Pidx::Last,
            cost: Credit::from(1),
        }
    }

    pub fn new(n1: Node, p1: Pidx, n2: Node, p2: Pidx) -> Self {
        Self {
            n1,
            n2,
            path_index_n1: p1,
            path_index_n2: p2,
            cost: Credit::from(1),
        }
    }

    pub fn with_cost(n1: Node, p1: Pidx, n2: Node, p2: Pidx, cost: Credit) -> Self {
        Self {
            n1,
            n2,
            path_index_n1: p1,
            path_index_n2: p2,
            cost,
        }
    }

    pub fn path_distance(&self) -> usize {
        self.path_index_n1.dist(&self.path_index_n2)
    }

    pub fn path_indices(&self) -> (Pidx, Pidx) {
        (
            self.path_index_n1.min(self.path_index_n2),
            self.path_index_n1.max(self.path_index_n2),
        )
    }

    pub fn to_tuple(&self) -> (Node, Node) {
        (self.n1, self.n2)
    }

    pub fn to_vec(&self) -> Vec<Node> {
        vec![self.n1, self.n2]
    }

    pub fn endpoint_at(&self, path_idx: Pidx) -> Option<Node> {
        if self.path_index_n1 == path_idx {
            Some(self.n1)
        } else if self.path_index_n2 == path_idx {
            Some(self.n2)
        } else {
            None
        }
    }

    pub fn endpoint_in(&self, nodes: &[Node]) -> Option<Node> {
        if nodes.contains(&self.n1) {
            Some(self.n1)
        } else if nodes.contains(&self.n2) {
            Some(self.n2)
        } else {
            None
        }
    }

    pub fn nodes_incident(&self, nodes: &[Node]) -> bool {
        nodes.contains(&self.n1) || nodes.contains(&self.n2)
    }

    pub fn one_sided_nodes_incident(&self, nodes: &[Node]) -> bool {
        (nodes.contains(&self.n1) && !nodes.contains(&self.n2))
            || (nodes.contains(&self.n2) && !nodes.contains(&self.n1))
    }

    pub fn between_sets(&self, nodes1: &[Node], nodes2: &[Node]) -> bool {
        (nodes1.contains(&self.n1) && nodes2.contains(&self.n2))
            || (nodes2.contains(&self.n1) && nodes1.contains(&self.n2))
    }

    pub fn node_incident(&self, n: &Node) -> bool {
        n == &self.n1 || n == &self.n2
    }

    pub fn other(&self, n: &Node) -> Option<Node> {
        if n == &self.n1 {
            Some(self.n2)
        } else if n == &self.n2 {
            return Some(self.n1);
        } else {
            return None;
        }
    }

    pub fn path_incident(&self, path_idx: Pidx) -> bool {
        path_idx == self.path_index_n1 || path_idx == self.path_index_n2
    }

    pub fn between_path_nodes(&self, path_idx1: Pidx, path_idx2: Pidx) -> bool {
        self.path_incident(path_idx1) && self.path_incident(path_idx2)
    }

    pub fn nodes_between_path_nodes(&self, idx1: Pidx, idx2: Pidx) -> (Node, Node) {
        if !self.between_path_nodes(idx1, idx2) {
            panic!("edge not between path nodes!")
        } else if self.path_index_n1 == idx1 {
            (self.n1, self.n2)
        } else {
            (self.n2, self.n1)
        }
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
