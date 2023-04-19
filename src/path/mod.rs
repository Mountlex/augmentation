mod enumerators;
mod extension;
mod instance;
mod proof;
mod pseudo_cycle;
mod tactics;
mod util;
mod utils;

use std::{cmp::Ordering, fmt::Display};

use itertools::Itertools;
pub use proof::prove_nice_path_progress;
pub use proof::PathProofOptions;

use crate::proof_tree::ProofNode;
use crate::Node;

use crate::comps::*;

use self::instance::InstanceProfile;

pub type PathProofNode = ProofNode<InstanceProfile>;

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

impl PartialEq for PathComp {
    fn eq(&self, other: &Self) -> bool {
        self.path_idx == other.path_idx
    }
}

#[derive(Clone, Debug)]
pub struct HalfAbstractEdge {
    source: Node,
    source_idx: Pidx,
}

impl Display for HalfAbstractEdge {
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
            .any(|(a, b)| (*a == u && *b == v) || (*a == v && *b == u))
    }

    // Checks whether this configuration is consistent with `consistent_npc` on the node set `consistent_nodes`.
    // This function returns true if for every pair of nodes from `consistent_nodes`, this configuration has the
    // same value for this pair as `consistent_npc`.
    #[allow(dead_code)]
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
        (0..len).map(Pidx::from).collect_vec()
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
