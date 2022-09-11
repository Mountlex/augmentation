mod enumerators;
mod proof;
mod tactics;
mod utils;

use std::fmt::Display;

use itertools::Itertools;
pub use proof::prove_nice_path_progress;

use crate::{
    comps::{Component, CreditInvariant, Graph, Node},
    path::utils::complex_cycle_value_base,
    Credit,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PathMatchingEdge(pub Node, pub PathMatchingHits);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathMatchingHits {
    Path(usize),
    Outside,
}

impl PathMatchingEdge {
    pub fn source(&self) -> Node {
        self.0.clone()
    }

    pub fn hit(&self) -> PathMatchingHits {
        self.1.clone()
    }

    pub fn hits_path(&self) -> Option<usize> {
        match self.1 {
            PathMatchingHits::Path(i) => Some(i),
            PathMatchingHits::Outside => None,
        }
    }

    pub fn hits_outside(&self) -> bool {
        matches!(self.1, PathMatchingHits::Outside)
    }
}

impl Display for PathMatchingEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.1 {
            PathMatchingHits::Path(j) => write!(f, "{} -- path[{}]", self.0, j),
            PathMatchingHits::Outside => write!(f, "{} -- outside", self.0),
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
pub struct NicePath {
    pub nodes: Vec<SuperNode>,
    pub graph: Graph,
}

impl NicePath {
    pub fn last_comp(&self) -> &Component {
        self.nodes.last().unwrap().get_comp()
    }
}

impl Display for NicePath {
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
pub struct PseudoCycle {
    nodes: Vec<SuperNode>,
}

impl PseudoCycle {
    fn value<C: CreditInvariant>(&self, credit_inv: C) -> Credit {
        let first_complex = self
            .nodes
            .iter()
            .enumerate()
            .find(|(_, n)| n.get_comp().is_complex())
            .map(|(i, _)| i);

        self.nodes
            .iter()
            .enumerate()
            .map(|(j, node)| {
                let lower_complex = first_complex.is_some() && first_complex.unwrap() < j;

                match node {
                    SuperNode::Abstract(abs) => abs.value(credit_inv.clone(), lower_complex),
                    SuperNode::Zoomed(zoomed) => zoomed.value(
                        credit_inv.clone(),
                        lower_complex,
                        zoomed.in_node.unwrap(),
                        zoomed.out_node.unwrap(),
                    ),
                }
            })
            .sum()
    }
}

impl Display for PseudoCycle {
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
pub enum PseudoNode {
    Abstract,
    Node(Node),
}

impl Display for PseudoNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PseudoNode::Abstract => write!(f, "AbstractNode"),
            PseudoNode::Node(n) => write!(f, "Real Node {}", n),
        }
    }
}

#[derive(Clone)]
pub struct ThreeMatching(
    pub PathMatchingEdge,
    pub PathMatchingEdge,
    pub PathMatchingEdge,
);

impl ThreeMatching {
    pub fn sources(&self) -> Vec<Node> {
        vec![self.0.source(), self.1.source(), self.2.source()]
    }

    pub fn to_vec(&self) -> Vec<PathMatchingEdge> {
        vec![self.0, self.1, self.2]
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

    fn value<C: CreditInvariant>(
        &self,
        credit_inv: C,
        lower_complex: bool,
        cycle_in: Node,
        cycle_out: Node,
    ) -> Credit {
        assert!(self.comp.graph().contains_node(cycle_in));
        assert!(self.comp.graph().contains_node(cycle_out));

        let comp_credit_minus_edge = credit_inv.credits(&self.comp) - Credit::from_integer(1);
        let complex = if lower_complex {
            credit_inv.complex_comp()
        } else {
            Credit::from_integer(0)
        };

        if self.npc.is_nice_pair(cycle_in, cycle_out) {
            if self.comp.is_complex() {
                complex
                    + complex_cycle_value_base(
                        credit_inv.clone(),
                        self.comp.graph(),
                        cycle_in,
                        cycle_out,
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
                        cycle_in,
                        cycle_out,
                    )
            } else {
                comp_credit_minus_edge
            }
        }
    }
}

impl Display for ZoomedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Node {} with in={:?} and out={:?}",
            self.comp, self.in_node, self.out_node
        )
    }
}
