mod enumerators;
mod proof;
mod tactics;
mod utils;

use std::{
    cmp::Ordering,
    fmt::Display,
    ops::{Index, IndexMut},
};

use itertools::Itertools;
pub use proof::prove_nice_path_progress;

use crate::{path::utils::complex_cycle_value_base, Credit, CreditInv, Node};

use crate::{comps::*, types::Edge};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct AbstractEdge {
    source_path: Pidx,
    source: Node,
    hit: PathHit,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathHit {
    Path(Pidx),
    Outside,
}

impl AbstractEdge {
    // source_path < hit !!!!
    pub fn new(source_path: Pidx, source: Node, hit: PathHit) -> Self {
        Self {
            source_path,
            source,
            hit,
        }
    }

    pub fn source_path(&self) -> Pidx {
        self.source_path
    }

    pub fn source(&self) -> Node {
        self.source.clone()
    }

    pub fn hit(&self) -> PathHit {
        self.hit.clone()
    }

    pub fn hits_path(&self) -> Option<Pidx> {
        match self.hit {
            PathHit::Path(i) => Some(i),
            PathHit::Outside => None,
        }
    }

    pub fn is_cycle_edge(&self) -> Option<(Pidx, Pidx)> {
        let j = self.source_path;
        match self.hit {
            PathHit::Path(i) if i.dist(&j) >= 2 => Some((j, i)),
            _ => None,
        }
    }

    pub fn hits_outside(&self) -> bool {
        matches!(self.hit, PathHit::Outside)
    }
}

impl Display for AbstractEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.hit {
            PathHit::Path(j) => write!(f, "({}--path[{}])", self.source, j),
            PathHit::Outside => write!(f, "({}--outside)", self.source),
        }
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
    fn empty() -> Self {
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

    pub fn path_idx(&self) -> Pidx {
        match self {
            SuperNode::Zoomed(n) => n.path_idx,
            SuperNode::Abstract(n) => n.path_idx,
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
    pub path_idx: Pidx,
}

impl AbstractNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    fn value(&self, credit_inv: &CreditInv, lower_complex: bool) -> Credit {
        match self.comp.comp_type() {
            CompType::Cycle(_) if !self.used => {
                if self.nice_pair {
                    credit_inv.credits(&self.comp)
                } else {
                    credit_inv.credits(&self.comp) - Credit::from_integer(1)
                }
            }
            CompType::Cycle(_) if self.used => {
                assert!(self.comp.is_c5());
                if self.in_not_out {
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
    in_node: Option<Node>,
    out_node: Option<Node>,
    pub connected_nodes: Vec<Node>,
    pub used: bool,
    pub path_idx: Pidx,
}

impl ZoomedNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    pub fn valid_in_out(&self, new_in: Node, new_out: Node, prelast: bool) -> bool {
        let c = self.get_comp();
        if c.is_c3() || c.is_c4() || c.is_complex() {
            self.npc.is_nice_pair(new_in, new_out)
        } else if c.is_c5() && prelast && self.used {
            new_in != new_out
        } else if c.is_c5() && prelast && !self.used {
            self.npc.is_nice_pair(new_in, new_out)
        } else {
            true
        }
    }

    pub fn valid_in(&self, new_in: Node, prelast: bool) -> bool {
        self.valid_in_out(new_in, self.out_node.unwrap(), prelast)
    }

    pub fn valid_out(&self, new_out: Node, prelast: bool) -> bool {
        self.valid_in_out(self.in_node.unwrap(), new_out, prelast)
    }

    pub fn set_in(&mut self, new_in: Node) {
        assert!(self.comp.contains(&new_in));
        self.in_node = Some(new_in)
    }

    pub fn set_out(&mut self, new_out: Node) {
        assert!(self.comp.contains(&new_out));
        self.out_node = Some(new_out)
    }

    fn value(&self, credit_inv: &CreditInv, lower_complex: bool) -> Credit {
        let nice_pair = self
            .npc
            .is_nice_pair(self.in_node.unwrap(), self.out_node.unwrap());

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

impl Display for ZoomedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[ {}: ", self.comp.short_name())?;
        if let Some(n) = self.in_node {
            write!(f, "in={}, ", n)?;
        }
        if let Some(n) = self.out_node {
            write!(f, "out={}, ", n)?;
        }
        write!(f, "used={} ]", self.used)
    }
}

#[derive(Clone, Debug)]
pub struct SelectedHitInstance {
    pub instance: AugmentedPathInstance,
    pub hit_comp_idx: Pidx,
    pub last_hit: bool,
}

#[derive(Clone, Debug)]
pub struct PseudoCycleInstance {
    pub instance: AugmentedPathInstance,
    pub cycle_edge: CycleEdge,
    pub pseudo_cycle: PseudoCycle,
}

#[derive(Clone, Debug)]
pub struct PathRearrangementInstance {
    pub instance: AugmentedPathInstance,
    pub cycle_edge: CycleEdge,
    pub start_idx: Pidx,
    pub extension: Vec<SuperNode>,
}

#[derive(Clone, Debug)]
pub enum CycleEdge {
    Fixed,
    Matching(AbstractEdge),
}

impl Display for CycleEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CycleEdge::Fixed => write!(f, "Fixed edges"),
            CycleEdge::Matching(e) => write!(f, "{}", e),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PseudoCycle {
    nodes: Vec<SuperNode>,
}

impl PseudoCycle {
    pub fn consecutive_end(&self) -> bool {
        let mut indices = self.nodes.iter().map(|n| n.path_idx().raw()).collect_vec();
        indices.sort();
        indices.contains(&0) && *indices.last().unwrap() == indices.len() - 1
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

impl Eq for Pidx { }

impl Display for Pidx {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Pidx::Last => write!(f, "Last"),
            Pidx::Prelast => write!(f, "Prelast"),
            Pidx::N(n) => write!(f, "Path[{}]", n),
        }
    }
}

#[derive(Clone, Debug)]
pub struct AugmentedPathInstance {
    nodes: Vec<SuperNode>,
    pub abstract_edges: Vec<AbstractEdge>,
    pub fixed_edges: Vec<Edge>,
}

impl AugmentedPathInstance {
    pub fn index_of_super_node(&self, node: Node) -> Pidx {
        let raw = self
            .nodes
            .iter()
            .enumerate()
            .find(|(_i, super_node)| super_node.get_comp().contains(&node))
            .unwrap()
            .0;

        Pidx::from(raw)
    }

    pub fn path_len(&self) -> usize {
        self.nodes.len()
    }

    pub fn all_outside_hits(&self) -> Vec<AbstractEdge> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_outside())
            .cloned()
            .collect_vec()
    }

    pub fn outside_hits_from(&self, path_idx: Pidx) -> Vec<AbstractEdge> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_outside() && e.source_path() == path_idx)
            .cloned()
            .collect_vec()
    }

    pub fn outside_edges_on(&self, path_idx: Pidx) -> Vec<Node> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_outside() && e.source_path() == path_idx)
            .map(|e| e.source())
            .collect_vec()
    }

    // Returns a list of nodes of path_idx which can have _one_ additional matching edge
    pub fn unmatched_nodes(&self, path_idx: Pidx) -> Vec<Node> {
        let comp = self[path_idx].get_comp();

        if let Component::Large(n) = comp {
            return vec![*n];
        }
        let fixed_incident = self.fixed_incident_edges(path_idx);
        let matching_sources = self.nodes_with_abstract_edges(path_idx);

        comp.matching_nodes()
            .into_iter()
            .filter(|n| {
                !(matching_sources.contains(n)
                    || fixed_incident.iter().any(|e| {
                        e.node_incident(n)
                            && !fixed_incident
                                .iter()
                                .any(|e2| !e2.node_incident(n) && e.edge_incident(e2))
                    }))
            })
            .cloned()
            .collect_vec()
    }

    pub fn nodes_with_fixed_edges(&self, path_idx: Pidx) -> Vec<Node> {
        let mut edge_endpoints = self
            .fixed_edges
            .iter()
            .flat_map(|e| e.endpoint_at(path_idx))
            .collect_vec();

        if let SuperNode::Zoomed(zoomed) = &self[path_idx] {
            if let Some(node) = zoomed.in_node {
                assert!(self[path_idx].get_comp().contains(&node));
                edge_endpoints.push(node)
            }
            if let Some(node) = zoomed.out_node {
                assert!(self[path_idx].get_comp().contains(&node));
                edge_endpoints.push(node)
            }
        }
        assert!(edge_endpoints
            .iter()
            .all(|n| self[path_idx].get_comp().contains(n)));
        edge_endpoints
    }

    pub fn nodes_with_abstract_edges(&self, path_idx: Pidx) -> Vec<Node> {
        let endpoints = self
            .abstract_edges
            .iter()
            .filter(|e| e.source_path() == path_idx)
            .map(|e| e.source())
            .collect_vec();

        assert!(endpoints
            .iter()
            .all(|n| self[path_idx].get_comp().contains(n)));
        endpoints
    }

    pub fn nodes_with_edges(&self, path_idx: Pidx) -> Vec<Node> {
        vec![
            self.nodes_with_abstract_edges(path_idx),
            self.nodes_with_fixed_edges(path_idx),
        ]
        .into_iter()
        .flatten()
        .unique()
        .collect_vec()
    }

    pub fn nodes_without_edges(&self, path_idx: Pidx) -> Vec<Node> {
        let edge_endpoints = self.nodes_with_edges(path_idx);

        self[path_idx]
            .get_comp()
            .graph()
            .nodes()
            .filter(|n| !edge_endpoints.contains(n))
            .collect_vec()
    }

    pub fn matching_edges_hit(&self, path_idx: Pidx) -> Vec<AbstractEdge> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_path() == Some(path_idx))
            .cloned()
            .collect_vec()
    }

    pub fn fix_matching_edge(
        &mut self,
        matching_edge: &AbstractEdge,
        hit_idx: Pidx,
        new_target: Node,
    ) {
        self.abstract_edges.drain_filter(|e| matching_edge == e);

        self.fixed_edges.push(Edge::new(
            new_target,
            hit_idx,
            matching_edge.source(),
            matching_edge.source_path(),
        ));
    }

    /// Returns fixed edges incident on `idx`
    pub fn fixed_incident_edges(&self, idx: Pidx) -> Vec<Edge> {
        self.fixed_edges
            .iter()
            .filter(|e| e.path_incident(idx))
            .cloned()
            .chain(
                vec![
                    self.path_edge(idx),
                    idx.succ().and_then(|left| self.path_edge(left)),
                ]
                .into_iter()
                .flatten(),
            )
            .collect_vec()
    }

    /// Returns path edge between `idx` and `idx + 1`
    fn path_edge(&self, idx: Pidx) -> Option<Edge> {
        if idx.raw() >= self.nodes.len() {
            return None;
        }
        if self[idx].is_zoomed() && self[idx.prec()].is_zoomed() {
            Some(Edge::new(
                self[idx.prec()].get_zoomed().out_node.unwrap(),
                idx.prec(),
                self[idx].get_zoomed().in_node.unwrap(),
                idx,
            ))
        } else {
            None
        }
    }

    pub fn fixed_edges_between(&self, idx1: Pidx, idx2: Pidx) -> Vec<Edge> {
        let mut edges = self
            .fixed_edges
            .iter()
            .filter(|&edge| edge.between_path_nodes(idx1, idx2))
            .cloned()
            .collect_vec();

        if idx1.dist(&idx2) == 1 {
            if let Some(path_edge) = self.path_edge(idx1.min(idx2)) {
                edges.push(path_edge);
            }
        }

        edges
    }
}

impl Index<Pidx> for AugmentedPathInstance {
    type Output = SuperNode;

    fn index(&self, index: Pidx) -> &Self::Output {
        &self.nodes[index.raw()]
    }
}

impl IndexMut<Pidx> for AugmentedPathInstance {
    fn index_mut(&mut self, index: Pidx) -> &mut Self::Output {
        &mut self.nodes[index.raw()]
    }
}

impl Display for AugmentedPathInstance {
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
