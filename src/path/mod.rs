mod enumerators;
mod proof;
mod tactics;
mod utils;
mod util;

use core::panic;
use std::{cmp::Ordering, fmt::Display};

use itertools::Itertools;
pub use proof::prove_nice_path_progress;

use crate::proof_tree::ProofNode;
use crate::{CreditInv, Node};

use crate::{comps::*, types::Edge};

use self::proof::Instance;

pub type PathProofNode = ProofNode<InstanceProfile>;

#[derive(Clone, Debug)]
pub struct InstPart {
    pub path_nodes: Vec<PathComp>,
    pub nice_pairs: Vec<(Node, Node)>,
    pub edges: Vec<Edge>,
    pub out_edges: Vec<Node>,
    pub rem_edges: Vec<MatchingEdge>,
    pub non_rem_edges: Vec<MatchingEdgeId>,
    pub connected_nodes: Vec<Node>,
}

impl InstPart {
    fn empty() -> InstPart {
        InstPart {
            path_nodes: vec![],
            nice_pairs: vec![],
            edges: vec![],
            out_edges: vec![],
            rem_edges: vec![],
            non_rem_edges: vec![],
            connected_nodes: vec![],
        }
    }

    pub fn new_path_comp(path_comp: PathComp) -> InstPart {
        InstPart {
            path_nodes: vec![path_comp],
            nice_pairs: vec![],
            edges: vec![],
            out_edges: vec![],
            rem_edges: vec![],
            non_rem_edges: vec![],
            connected_nodes: vec![],
        }
    }
}

impl Display for InstPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Inst [")?;
        if !self.path_nodes.is_empty() {
            write!(f, "PathComps: ")?;
            write!(f, "{}", self.path_nodes.iter().join(", "))?;
            write!(f, ", ")?;
        }
        if !self.edges.is_empty() {
            write!(f, "Edges: ")?;
            write!(f, "{}", self.edges.iter().join(", "))?;
            write!(f, ", ")?;
        }
        if !self.nice_pairs.is_empty() {
            write!(f, "NicePairs: ")?;
            write!(
                f,
                "{:?}",
                self.nice_pairs
                    .iter()
                    .map(|n| format!("{:?}", n))
                    .join(", ")
            )?;
            write!(f, ", ")?;
        }
        if !self.out_edges.is_empty() {
            write!(f, "Outside: ")?;
            write!(f, "{}", self.out_edges.iter().join(", "))?;
            write!(f, ", ")?;
        }
        if !self.rem_edges.is_empty() {
            write!(f, "Rem: ")?;
            write!(f, "{}", self.rem_edges.iter().join(", "))?;
            write!(f, ", ")?;
        }
        if !self.non_rem_edges.is_empty() {
            write!(f, "Non-Rem-Ids: ")?;
            write!(f, "{}", self.non_rem_edges.iter().join(", "))?;
            write!(f, ", ")?;
        }

        write!(f, "]")
    }
}

#[derive(Clone, Debug)]
pub struct InstanceContext {
    pub inv: CreditInv,
    pub comps: Vec<PathNode>,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct InstanceProfile {
    pub comp_types: Vec<CompType>,
    pub success: bool,
}

impl InstanceProfile {
    pub fn includes(&self, other: &InstanceProfile) -> bool {
        other.comp_types.len() < self.comp_types.len()
            && self
                .comp_types
                .iter()
                .zip(other.comp_types.iter())
                .filter(|(t1, t2)| t1 != t2)
                .count()
                == 0
    }
}

impl Display for InstanceProfile {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.comp_types.iter().join(" -- "))
    }
}

impl Instance {
    pub fn get_profile(&self, success: bool) -> InstanceProfile {
        let comps = self.path_nodes().map(|n| n.comp.comp_type()).collect_vec();
        InstanceProfile {
            comp_types: comps,
            success,
        }
    }

    fn path_nodes<'a>(&'a self) -> impl Iterator<Item = &'a PathComp> {
        self.inst_parts().flat_map(|part| part.path_nodes.iter())
    }

    fn nice_pairs<'a>(&'a self) -> impl Iterator<Item = &'a (Node, Node)> {
        self.inst_parts().flat_map(|part| part.nice_pairs.iter())
    }

    fn out_edges<'a>(&'a self) -> impl Iterator<Item = &'a Node> {
        self.inst_parts().flat_map(|part| part.out_edges.iter())
    }

    fn connected_nodes<'a>(&'a self) -> impl Iterator<Item = &'a Node> {
        self.inst_parts()
            .flat_map(|part| part.connected_nodes.iter())
    }

    fn rem_edges<'a>(&'a self) -> Vec<MatchingEdge> {
        let mut rem_edges: Vec<MatchingEdge> = vec![];
        for part in self.inst_parts() {
            if part.non_rem_edges.len() > 0 {
                for non_rem_id in &part.non_rem_edges {
                    if let Some((pos, _)) = rem_edges
                        .iter()
                        .find_position(|edge| &edge.id == non_rem_id)
                    {
                        rem_edges.swap_remove(pos);
                    }
                }
            }
            rem_edges.append(&mut part.rem_edges.iter().cloned().collect_vec());
        }

        rem_edges
    }

    fn npc<'a>(&'a self) -> NicePairConfig {
        let tuples = self
            .inst_parts()
            .flat_map(|part| part.nice_pairs.iter())
            .unique()
            .cloned()
            .collect_vec();
        NicePairConfig { nice_pairs: tuples }
    }

    fn implied_edges<'a>(&'a self) -> impl Iterator<Item = &'a Edge> {
        self.inst_parts().flat_map(|part| part.edges.iter())
    }

    fn all_edges<'a>(&'a self) -> Vec<Edge> {
        let mut implied_edges = self.implied_edges().cloned().collect_vec();
        let nodes = self.path_nodes().collect_vec();
        for w in nodes.windows(2) {
            implied_edges.push(Edge::new(
                w[0].in_node.unwrap(),
                w[0].path_idx,
                w[1].out_node.unwrap(),
                w[1].path_idx,
            ));
        }

        implied_edges
    }
}

#[derive(Clone, Debug)]
pub enum PathNode {
    Used(Component),
    Unused(Component),
}

impl PathNode {
    pub fn is_used(&self) -> bool {
        matches!(self, Self::Used(_))
    }

    pub fn get_comp(&self) -> &Component {
        match self {
            PathNode::Used(c) | PathNode::Unused(c) => c,
        }
    }

    fn short_name(&self) -> String {
        match self {
            PathNode::Used(c) => format!("aided-{}", c.short_name()),
            PathNode::Unused(c) => c.short_name(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Rearrangement {
    pub extension: Vec<(Option<Node>, Pidx, Option<Node>)>,
}

impl Display for Rearrangement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let inner = self
            .extension
            .iter()
            .map(|(l, n, r)| format!("{:?}-[{}]-{:?}", l, n, r))
            .join(", ");
        write!(f, "Ext [ {} ]", inner)
    }
}

#[derive(Clone, Debug)]
pub struct PseudoCycle {
    pub cycle: Vec<(Node, CycleComp, Node)>,
}

impl PseudoCycle {
    fn consecutive_end(&self) -> bool {
        let mut indices = self
            .cycle
            .iter()
            .flat_map(|(_, cycle_comp, _)| {
                if let CycleComp::PathComp(idx) = cycle_comp {
                    Some(idx.raw())
                } else {
                    None
                }
            })
            .collect_vec();
        indices.sort();
        indices.contains(&0) && *indices.last().unwrap() == indices.len() - 1
    }
}

impl Display for PseudoCycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let inner = self
            .cycle
            .iter()
            .map(|(l, n, r)| match n {
                CycleComp::PathComp(idx) => format!("{}-[{}]-{}", l, idx, r),
                CycleComp::Rem => format!("REM"),
            })
            .join(", ");
        write!(f, "PC [ {} ] (length={})", inner, self.cycle.len())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CycleComp {
    PathComp(Pidx),
    Rem,
}

impl CycleComp {
    pub fn to_idx(&self) -> &Pidx {
        match self {
            CycleComp::PathComp(idx) => idx,
            CycleComp::Rem => panic!("Rem has no idx"),
        }
    }

    pub fn is_rem(&self) -> bool {
        matches!(self, CycleComp::Rem)
    }
}

impl Display for CycleComp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CycleComp::PathComp(idx) => write!(f, "{}", idx),
            CycleComp::Rem => write!(f, "REM"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PathComp {
    comp: Component,
    in_node: Option<Node>,
    out_node: Option<Node>,
    used: bool,
    path_idx: Pidx,
}

impl Display for PathComp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let used = if self.used { ", used" } else { "" };
        match (self.in_node, self.out_node) {
            (None, None) => write!(
                f,
                "[{}, idx={}{}]",
                self.comp.short_name(),
                self.path_idx,
                used
            ),
            (None, Some(out)) => write!(
                f,
                "[{}, out={}, idx={}{}]",
                self.comp.short_name(),
                out,
                self.path_idx,
                used
            ),
            (Some(in_n), None) => write!(
                f,
                "[{}, in={}, idx={}{}]",
                self.comp.short_name(),
                in_n,
                self.path_idx,
                used
            ),
            (Some(in_n), Some(out_n)) => write!(
                f,
                "[{}, in={}, out={}, idx={}{}]",
                self.comp.short_name(),
                in_n,
                out_n,
                self.path_idx,
                used
            ),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MatchingEdgeId(pub u128);

impl MatchingEdgeId {
    pub fn inc(&mut self) {
        self.0 += 1;
    }
}

impl Display for MatchingEdgeId {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "NonRem({})", self.0)
    }
}

#[derive(Clone, Debug)]
pub struct MatchingEdge {
    source: Node,
    source_idx: Pidx,
    id: MatchingEdgeId,
    matching: bool,
}

impl Display for MatchingEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-REM", self.source)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
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
    pub fn empty() -> Self {
        NicePairConfig { nice_pairs: vec![] }
    }

    pub fn is_nice_pair(&self, u: Node, v: Node) -> bool {
        self.nice_pairs
            .iter()
            .find(|(a, b)| (*a == u && *b == v) || (*a == v && *b == u))
            .is_some()
    }

    /// Checks whether this configuration is consistent with `consistent_npc` on the node set `consistent_nodes`.
    /// This function returns true if for every pair of nodes from `consistent_nodes`, this configuration has the
    /// same value for this pair as `consistent_npc`.
    pub fn is_consistent_with(
        &self,
        consistent_npc: &NicePairConfig,
        consistent_nodes: &[Node],
    ) -> bool {
        consistent_nodes
            .iter()
            .tuple_combinations::<(_, _)>()
            .all(|(u, v)| self.is_nice_pair(*u, *v) == consistent_npc.is_nice_pair(*u, *v))
    }
}

#[derive(Copy, Clone, Debug, Hash)]
pub enum Pidx {
    Last,
    Prelast,
    N(usize),
}

impl Pidx {
    fn is_last(&self) -> bool {
        matches!(self, Pidx::Last)
    }
    fn is_prelast(&self) -> bool {
        matches!(self, Pidx::Prelast)
    }

    pub fn range(len: usize) -> Vec<Pidx> {
        (0..len).map(|i| Pidx::from(i)).collect_vec()
    }

    pub fn raw(&self) -> usize {
        match self {
            Pidx::Last => 0,
            Pidx::Prelast => 1,
            Pidx::N(n) => *n,
        }
    }

    pub fn prec(&self) -> Pidx {
        if let Pidx::Last = self {
            Pidx::Prelast
        } else {
            Pidx::N(self.raw() + 1)
        }
    }

    pub fn succ(&self) -> Option<Pidx> {
        match self {
            Pidx::Last => None,
            Pidx::Prelast => Some(Pidx::Last),
            Pidx::N(n) if *n == 2 => Some(Pidx::Prelast),
            Pidx::N(n) => Some(Pidx::N(n - 1)),
        }
    }

    pub fn dist(&self, other: &Pidx) -> usize {
        self.raw().max(other.raw()) - self.raw().min(other.raw())
    }
}

impl From<usize> for Pidx {
    fn from(n: usize) -> Self {
        if n == 0 {
            Pidx::Last
        } else if n == 1 {
            Pidx::Prelast
        } else {
            Pidx::N(n)
        }
    }
}

impl PartialOrd for Pidx {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.raw().partial_cmp(&other.raw())
    }
}

impl Ord for Pidx {
    fn cmp(&self, other: &Self) -> Ordering {
        self.raw().cmp(&other.raw())
    }
}

impl PartialEq for Pidx {
    fn eq(&self, other: &Self) -> bool {
        self.raw().eq(&other.raw())
    }
}

impl Eq for Pidx {}

impl Display for Pidx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pidx::Last => write!(f, "Last"),
            Pidx::Prelast => write!(f, "Prelast"),
            Pidx::N(n) => write!(f, "Path[{}]", n),
        }
    }
}
