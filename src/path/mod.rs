mod enumerators;
mod proof;
mod tactics;
mod utils;

use std::fmt::Display;

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
    pub fn to_zoomed(&self) -> &ZoomedNode {
        match self {
            SuperNode::Zoomed(n) => n,
            SuperNode::Abstract(_) => panic!("Super node is not zoomed!"),
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

#[derive(Clone, Debug)]
pub struct Matching3 {
    pub source_comp_idx: usize,
    pub path_edge_left: Option<MatchingEdge>,
    pub path_edge_right: Option<MatchingEdge>,
    pub other_edges: Vec<MatchingEdge>,
}

impl Matching3 {
    pub fn outside_hits(&self) -> Vec<MatchingEdge> {
        self.other_edges
            .iter()
            .filter(|e| e.hits_outside())
            .cloned()
            .collect_vec()
    }

    pub fn sources(&self) -> Vec<Node> {
        let mut sources = self.other_edges.iter().map(|e| e.source()).collect_vec();
        if let Some(e) = self.path_edge_left {
            sources.push(e.source())
        }
        if let Some(e) = self.path_edge_right {
            sources.push(e.source())
        }
        sources
    }

    pub fn to_vec(&self) -> Vec<MatchingEdge> {
        vec![self.path_edge_left, self.path_edge_right]
            .into_iter()
            .flatten()
            .chain(self.other_edges.iter().cloned())
            .collect()
    }
}

impl Display for Matching3 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Matching for path[{}]: ", self.source_comp_idx)?;
        if let Some(e) = self.path_edge_left {
            write!(f, "left = {}, ", e)?;
        }
        if let Some(e) = self.path_edge_right {
            write!(f, "right = {}, ", e)?;
        }
        write!(
            f,
            "others = [{}]",
            self.other_edges.iter().map(|e| format!("{}", e)).join(", ")
        )
    }
}

#[derive(Debug, Clone)]
pub struct AbstractNode {
    pub comp: Component,
    pub nice_pair: bool,
    pub used: bool,
}

impl AbstractNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    fn value<C: CreditInvariant>(&self, credit_inv: C, lower_complex: bool) -> Credit {
        let comp_credit_minus_edge = credit_inv.credits(&self.comp) - Credit::from_integer(1);
        let complex = if lower_complex {
            credit_inv.complex_comp()
        } else {
            Credit::from_integer(0)
        };

        if self.nice_pair {
            if self.comp.is_complex() {
                complex + credit_inv.complex_black(4)
            } else {
                comp_credit_minus_edge + Credit::from_integer(1)
            }
        } else {
            if self.comp.is_complex() {
                complex + credit_inv.complex_black(2)
            } else {
                comp_credit_minus_edge
            }
        }
    }
}

impl Display for AbstractNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.nice_pair {
            write!(f, "Abstract Node {} with nice pair", self.comp)
        } else {
            write!(f, "Abstract Node {}", self.comp)
        }
    }
}

#[derive(Debug, Clone)]
pub struct ZoomedNode {
    pub comp: Component,
    pub npc: NicePairConfig,
    pub in_node: Option<Node>,
    pub out_node: Option<Node>,
}

impl ZoomedNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    fn value<C: CreditInvariant>(&self, credit_inv: C, lower_complex: bool) -> Credit {
        let comp_credit_minus_edge = credit_inv.credits(&self.comp) - Credit::from_integer(1);
        let complex = if lower_complex {
            credit_inv.complex_comp()
        } else {
            Credit::from_integer(0)
        };

        if self
            .npc
            .is_nice_pair(self.in_node.unwrap(), self.out_node.unwrap())
        {
            if self.comp.is_complex() {
                complex
                    + complex_cycle_value_base(
                        credit_inv.clone(),
                        self.comp.graph(),
                        self.in_node.unwrap(),
                        self.out_node.unwrap(),
                    )
            } else {
                comp_credit_minus_edge + Credit::from_integer(1)
            }
        } else {
            if self.comp.is_complex() {
                complex
                    + complex_cycle_value_base(
                        credit_inv.clone(),
                        self.comp.graph(),
                        self.in_node.unwrap(),
                        self.out_node.unwrap(),
                    )
            } else {
                comp_credit_minus_edge
            }
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
            write!(f, "out={}", n)?;
        }
        write!(f, "npc={} ]", self.npc)
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
pub struct PathMatchingInstance {
    pub path: PathInstance,
    pub matching: Matching3,
}

#[derive(Clone)]
pub struct SelectedHitInstance {
    pub path_matching: PathMatchingInstance,
    pub hit_comp_idx: usize,
    pub matched: Vec<MatchingEdge>,
}

#[derive(Clone)]
pub struct SelectedMatchingInstance {
    pub path_matching: PathMatchingInstance,
    pub hit_comp_idx: usize,
    pub matched: Vec<Edge>,
}
