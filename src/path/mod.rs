mod enumerators;
mod proof;
mod tactics;
mod utils;

use std::{cmp::Ordering, fmt::Display};

use itertools::Itertools;
pub use proof::prove_nice_path_progress;

use crate::{path::utils::complex_cycle_value_base, Credit, CreditInv, Node};

use crate::{comps::*, types::Edge};

use self::proof::Instance;

#[derive(Clone, Debug)]
pub struct InstPart {
    pub path_nodes: Vec<PathComp>,
    pub nice_pairs: Vec<(Node, Node)>,
    pub edges: Vec<Edge>,
    pub out_edges: Vec<Node>,
    pub rem_edges: Vec<MatchingEdge>,
    pub non_rem_edges: Vec<MatchingEdge>,
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

    fn new_path_comp(path_comp: PathComp) -> InstPart {
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
        todo!()
    }
}

#[derive(Clone, Debug)]
pub struct InstanceContext {
    pub inv: CreditInv,
    pub comps: Vec<PathNode>,
}

impl Instance {
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

    fn rem_edges<'a>(&'a self) -> Vec<&'a MatchingEdge> {
        let mut rem_edges: Vec<&'a MatchingEdge> = vec![];
        for part in self.inst_parts() {
            let non_sources = &part
                .non_rem_edges
                .iter()
                .map(|edge| edge.source)
                .collect_vec();
            if non_sources.len() > 0 {
                rem_edges.drain_filter(|edge| non_sources.contains(&edge.source));
            }
            rem_edges.append(&mut part.rem_edges.iter().collect_vec());
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
pub struct PathComp {
    comp: Component,
    in_node: Option<Node>,
    out_node: Option<Node>,
    used: bool,
    path_idx: Pidx,
}

impl PathComp {
    fn value(&self, npc: &NicePairConfig, credit_inv: &CreditInv, lower_complex: bool) -> Credit {
        let nice_pair = npc.is_nice_pair(self.in_node.unwrap(), self.out_node.unwrap());

        match self.comp.comp_type() {
            CompType::Cycle(_) if !self.used => {
                if nice_pair {
                    credit_inv.credits(&self.comp)
                } else {
                    credit_inv.credits(&self.comp) - Credit::from_integer(1)
                }
            }
            CompType::Cycle(_) if self.used => {
                assert!(self.comp.is_c5());
                if self.in_node != self.out_node {
                    credit_inv.two_ec_credit(4) + credit_inv.two_ec_credit(5)
                        - Credit::from_integer(1)
                } else {
                    credit_inv.credits(&self.comp) - Credit::from_integer(1)
                }
            }
            CompType::Large => credit_inv.credits(&self.comp) - Credit::from_integer(1),
            CompType::Complex => {
                let complex = if lower_complex {
                    credit_inv.complex_comp()
                } else {
                    Credit::from_integer(0)
                };
                if nice_pair {
                    complex
                        + complex_cycle_value_base(
                            credit_inv,
                            &self.comp.graph(),
                            self.in_node.unwrap(),
                            self.out_node.unwrap(),
                        )
                } else {
                    complex
                        + complex_cycle_value_base(
                            credit_inv,
                            &self.comp.graph(),
                            self.in_node.unwrap(),
                            self.out_node.unwrap(),
                        )
                }
            }
            _ => panic!(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct MatchingEdge {
    source: Node,
    source_idx: Pidx,
    matching: bool,
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

pub fn valid_in_out_npc(
    c: &Component,
    npc: &NicePairConfig,
    new_in: Node,
    new_out: Node,
    prelast: bool,
    used: bool,
) -> bool {
    if c.is_c3() || c.is_c4() || c.is_complex() {
        npc.is_nice_pair(new_in, new_out)
    } else if c.is_c5() && prelast && used {
        new_in != new_out
    } else if c.is_c5() && prelast && !used {
        npc.is_nice_pair(new_in, new_out)
    } else {
        true
    }
}

#[derive(Copy, Clone, Debug)]
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
