mod enumerators;
mod proof;
mod tactics;
mod utils;

use std::{
    fmt::Display,
    ops::{Index, IndexMut},
};

use itertools::Itertools;
pub use proof::prove_nice_path_progress;

use crate::{
    comps::{Component, CreditInvariant, Node},
    path::utils::complex_cycle_value_base,
    types::Edge,
    Credit,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MatchingEdge(pub Node, pub PathHit);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathHit {
    Path(usize),
    Outside,
}

impl MatchingEdge {
    pub fn source(&self) -> Node {
        self.0.clone()
    }

    pub fn hit(&self) -> PathHit {
        self.1.clone()
    }

    pub fn hits_path(&self) -> Option<usize> {
        match self.1 {
            PathHit::Path(i) => Some(i),
            PathHit::Outside => None,
        }
    }

    pub fn hits_outside(&self) -> bool {
        matches!(self.1, PathHit::Outside)
    }
}

impl Display for MatchingEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.1 {
            PathHit::Path(j) => write!(f, "({}--path[{}])", self.0, j),
            PathHit::Outside => write!(f, "({}--outside)", self.0),
        }
    }
}

#[derive(Debug, Clone)]
pub struct NicePairConfig {
    nice_pairs: Vec<(Node, Node)>,
}

impl Display for NicePairConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[ ")?;
        write!(
            f,
            "{}",
            self.nice_pairs
                .iter()
                .map(|(a, b)| format!("({}, {})", a, b))
                .join(", ")
        )?;
        write!(f, " ]")
    }
}

impl NicePairConfig {
    fn empty() -> Self {
        NicePairConfig { nice_pairs: vec![] }
    }

    pub fn merge(self, other: NicePairConfig) -> NicePairConfig {
        NicePairConfig {
            nice_pairs: vec![self.nice_pairs, other.nice_pairs].concat(),
        }
    }

    pub fn add_nice_pair(&mut self, u: Node, v: Node) {
        self.nice_pairs.push((u, v))
    }

    pub fn is_nice_pair(&self, u: Node, v: Node) -> bool {
        self.nice_pairs
            .iter()
            .find(|(a, b)| (*a == u && *b == v) || (*a == v && *b == u))
            .is_some()
    }
}

#[derive(Debug, Clone)]
pub enum SuperNode {
    Zoomed(ZoomedNode),
    Abstract(AbstractNode),
}

impl SuperNode {
    pub fn get_zoomed(&self) -> &ZoomedNode {
        match self {
            SuperNode::Zoomed(n) => n,
            SuperNode::Abstract(_) => panic!("Super node is not zoomed!"),
        }
    }

    pub fn is_zoomed(&self) -> bool {
        matches!(self, Self::Zoomed(_))
    }
    pub fn used(&self) -> bool {
        match self {
            SuperNode::Zoomed(c) => c.used,
            SuperNode::Abstract(c) => c.used,
        }
    }

    pub fn get_abstract(&self) -> &AbstractNode {
        match self {
            SuperNode::Zoomed(_) => panic!("Super node is not abstract!"),
            SuperNode::Abstract(n) => n,
        }
    }

    pub fn get_zoomed_mut(&mut self) -> &mut ZoomedNode {
        match self {
            SuperNode::Zoomed(n) => n,
            SuperNode::Abstract(_) => panic!("Super node is not zoomed!"),
        }
    }

    pub fn get_abstract_mut(&mut self) -> &mut AbstractNode {
        match self {
            SuperNode::Zoomed(_) => panic!("Super node is not abstract!"),
            SuperNode::Abstract(n) => n,
        }
    }

    pub fn get_comp(&self) -> &Component {
        match self {
            SuperNode::Zoomed(node) => node.get_comp(),
            SuperNode::Abstract(node) => node.get_comp(),
        }
    }
}

impl Display for SuperNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SuperNode::Zoomed(n) => write!(f, "{}", n),
            SuperNode::Abstract(n) => write!(f, "{}", n),
        }
    }
}



#[derive(Debug, Clone)]
pub struct AbstractNode {
    pub comp: Component,

    pub in_not_out: bool,
    pub nice_pair: bool,
    pub used: bool,
}

impl AbstractNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    fn value<C: CreditInvariant>(&self, credit_inv: C, lower_complex: bool) -> Credit {
        match self.comp {
            Component::Cycle(_) if !self.used => {
                if self.nice_pair {
                    credit_inv.credits(&self.comp)
                } else {
                    credit_inv.credits(&self.comp) - Credit::from_integer(1)
                }
            }
            Component::Cycle(_) if self.used => {
                assert!(self.comp.is_c5());
                if self.in_not_out {
                    credit_inv.two_ec_credit(4) + credit_inv.two_ec_credit(5)
                        - Credit::from_integer(1)
                } else {
                    credit_inv.credits(&self.comp) - Credit::from_integer(1)
                }
            }
            Component::Large(_) => credit_inv.credits(&self.comp) - Credit::from_integer(1),
            Component::Complex(_, _, _) => {
                let complex = if lower_complex {
                    credit_inv.complex_comp()
                } else {
                    Credit::from_integer(0)
                };
                if self.nice_pair {
                    complex + credit_inv.complex_black(4)
                } else {
                    complex + credit_inv.complex_black(2)
                }
            }
            _ => panic!(),
        }
    }
}

impl Display for AbstractNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "[ {} np={}, used={}, in_not_out={} ]",
            self.comp, self.nice_pair, self.used, self.in_not_out
        )
    }
}

#[derive(Debug, Clone)]
pub struct ZoomedNode {
    pub comp: Component,
    pub npc: NicePairConfig,
    pub in_node: Option<Node>,
    pub out_node: Option<Node>,
    pub used: bool,
}

impl ZoomedNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    fn value<C: CreditInvariant>(&self, credit_inv: C, lower_complex: bool) -> Credit {
        let nice_pair = self
            .npc
            .is_nice_pair(self.in_node.unwrap(), self.out_node.unwrap());

        match self.comp {
            Component::Cycle(_) if !self.used => {
                if nice_pair {
                    credit_inv.credits(&self.comp)
                } else {
                    credit_inv.credits(&self.comp) - Credit::from_integer(1)
                }
            }
            Component::Cycle(_) if self.used => {
                assert!(self.comp.is_c5());
                if self.in_node != self.out_node {
                    credit_inv.two_ec_credit(4) + credit_inv.two_ec_credit(5)
                        - Credit::from_integer(1)
                } else {
                    credit_inv.credits(&self.comp) - Credit::from_integer(1)
                }
            }
            Component::Large(_) => credit_inv.credits(&self.comp) - Credit::from_integer(1),
            Component::Complex(_, _, _) => {
                let complex = if lower_complex {
                    credit_inv.complex_comp()
                } else {
                    Credit::from_integer(0)
                };
                if nice_pair {
                    complex
                        + complex_cycle_value_base(
                            credit_inv.clone(),
                            self.comp.graph(),
                            self.in_node.unwrap(),
                            self.out_node.unwrap(),
                        )
                } else {
                    complex
                        + complex_cycle_value_base(
                            credit_inv.clone(),
                            self.comp.graph(),
                            self.in_node.unwrap(),
                            self.out_node.unwrap(),
                        )
                }
            }
            _ => panic!(),
        }
    }
}

impl Display for ZoomedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[ {}: ", self.comp)?;
        if let Some(n) = self.in_node {
            write!(f, "in={}, ", n)?;
        }
        if let Some(n) = self.out_node {
            write!(f, "out={}, ", n)?;
        }
        write!(f, "npc={}, used={} ]", self.npc, self.used)
    }
}

#[derive(Clone, Debug)]
pub struct PathInstance {
    pub nodes: Vec<SuperNode>,
}

impl PathInstance {
    pub fn last_comp(&self) -> &Component {
        self.nodes.last().unwrap().get_comp()
    }

    pub fn index_of_super_node(&self, node: Node) -> usize {
        self.nodes
            .iter()
            .enumerate()
            .find(|(i, super_node)| super_node.get_comp().nodes().contains(&node))
            .unwrap()
            .0
    }
}

impl Index<usize> for PathInstance {
    type Output = SuperNode;

    fn index(&self, index: usize) -> &Self::Output {
        &self.nodes[index]
    }
}

impl IndexMut<usize> for PathInstance {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.nodes[index]
    }
}

impl Display for PathInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        write!(
            f,
            "{}",
            self.nodes
                .iter()
                .map(|node| format!("{}", node))
                .join(" -- ")
        )?;
        write!(f, "]")
    }
}



#[derive(Clone, Debug)]
pub struct SelectedHitInstance {
    pub instance: AugmentedPathInstance,
    pub hit_comp_idx: usize,
}

#[derive(Clone, Debug)]
pub struct PseudoCycleInstance {
    pub path_matching: AugmentedPathInstance,
    pub cycle_edge: CycleEdge,
    pub pseudo_cycle: PseudoCycle,
}

#[derive(Clone, Debug)]
pub enum CycleEdge {
    Fixed(Edge),
    Matching(MatchingEdge),
}

#[derive(Clone, Debug)]
pub struct PseudoCycle {
    nodes: Vec<SuperNode>,
}

#[derive(Clone, Debug)]
pub struct AugmentedPathInstance {
    pub path: PathInstance,
    pub non_path_matching_edges: Vec<MatchingEdge>,
    pub fixed_edge: Vec<Edge>,
}

impl AugmentedPathInstance {
    pub fn outside_hits(&self) -> Vec<MatchingEdge> {
        self.non_path_matching_edges
            .iter()
            .filter(|e| e.hits_outside())
            .cloned()
            .collect_vec()
    }

    pub fn all_edge_endpoints(&self, node_idx: usize) -> Vec<Node> {
        let mut edge_endpoints = self
            .non_path_matching_edges
            .iter()
            .map(|n| n.source())
            .chain(self.fixed_edge.iter().flat_map(|e| vec![e.0, e.1]))
            .collect_vec();

        if let SuperNode::Zoomed(zoomed) = &self.path[node_idx] {
            if let Some(node) = zoomed.in_node {
                edge_endpoints.push(node)
            }
            if let Some(node) = zoomed.out_node {
                edge_endpoints.push(node)
            }
        }

        edge_endpoints.sort();
        edge_endpoints.dedup();
        edge_endpoints
    }

    pub fn free_nodes(&self, node_idx: usize) -> Vec<Node> {
        let edge_endpoints = self.all_edge_endpoints(node_idx);

        self.path[node_idx]
            .get_comp()
            .graph()
            .nodes()
            .filter(|n| !edge_endpoints.contains(n))
            .collect_vec()
    }

    pub fn matching_edges_hit(&self, node_idx: usize) -> Vec<MatchingEdge> {
        self.non_path_matching_edges
            .iter()
            .filter(|e| e.hits_path() == Some(node_idx))
            .cloned()
            .collect_vec()
    }

    pub fn fix_matching_edge(&mut self, source: Node, hit_idx: usize, new_target: Node) {
        let matching_edge = self
            .non_path_matching_edges
            .drain_filter(|e| e.source() == source && e.hits_path() == Some(hit_idx))
            .collect_vec()[0];

        self.fixed_edge
            .push(Edge(new_target, matching_edge.source()));
    }

    pub fn path_edge(&self, idx: usize) -> Option<Edge> {
        if self.path[idx - 1].is_zoomed() && self.path[idx].is_zoomed() {
            Some(Edge(
                self.path[idx - 1].get_zoomed().out_node.unwrap(),
                self.path[idx].get_zoomed().in_node.unwrap(),
            ))
        } else {
            None
        }
    }

    pub fn swap_path_edge(&mut self, new_path_edge: Edge, path_edge_idx: usize) {
        assert!(self.path[path_edge_idx - 1].is_zoomed() && self.path[path_edge_idx].is_zoomed());
        assert!(self.fixed_edge.contains(&new_path_edge));

        let old_path_edge = self.path_edge(path_edge_idx).unwrap();
        self.path[path_edge_idx - 1].get_zoomed_mut().out_node = Some(new_path_edge.0);
        self.path[path_edge_idx].get_zoomed_mut().in_node = Some(new_path_edge.1);

        self.fixed_edge.drain_filter(|e| *e == new_path_edge);
        self.fixed_edge.push(old_path_edge);
    }

    pub fn fixed_edges_between(&self, left: usize, right: usize) -> Vec<Edge> {
        let left_nodes = self.path[left].get_comp().nodes();
        let right_nodes = self.path[right].get_comp().nodes();
        let mut edges = self
            .fixed_edge
            .iter()
            .filter(|&edge| {
                (left_nodes.contains(&edge.0) && right_nodes.contains(&edge.1))
                    || (left_nodes.contains(&edge.1) && right_nodes.contains(&edge.0))
            })
            .cloned()
            .collect_vec();

        if left + 1 == right {
            if let Some(path_edge) = self.path_edge(right) {
                edges.push(path_edge);
            }
        }
        edges
    }
}
