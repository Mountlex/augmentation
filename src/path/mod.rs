mod enumerators;
mod proof;
mod tactics;
mod utils;

use std::{
    fmt::Display,
    ops::{Index, IndexMut},
};

use itertools::Itertools;
use petgraph::algo::Cycle;
pub use proof::prove_nice_path_progress;

use crate::{
    comps::{CompType, Component, CreditInvariant, Node},
    path::utils::complex_cycle_value_base,
    types::Edge,
    Credit,
};

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct MatchingEdge {
    source_path: usize,
    source: Node,
    hit: PathHit,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathHit {
    Path(usize),
    Outside,
}

impl MatchingEdge {
    pub fn new(source_path: usize, source: Node, hit: PathHit) -> Self {
        Self {
            source_path,
            source,
            hit,
        }
    }

    pub fn source_path(&self) -> usize {
        self.source_path
    }

    pub fn source(&self) -> Node {
        self.source.clone()
    }

    pub fn hit(&self) -> PathHit {
        self.hit.clone()
    }

    pub fn hits_path(&self) -> Option<usize> {
        match self.hit {
            PathHit::Path(i) => Some(i),
            PathHit::Outside => None,
        }
    }

    pub fn is_cycle_edge(&self) -> Option<(usize, usize)> {
        let j = self.source_path;
        match self.hit {
            PathHit::Path(i) if i.max(j) - i.min(j) >= 2 => Some((i, j)),
            _ => None,
        }
    }

    pub fn hits_outside(&self) -> bool {
        matches!(self.hit, PathHit::Outside)
    }
}

impl Display for MatchingEdge {
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
    pub in_node: Option<Node>,
    pub out_node: Option<Node>,
    pub connected_nodes: Vec<Node>,
    pub used: bool,
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

    fn value<C: CreditInvariant>(&self, credit_inv: C, lower_complex: bool) -> Credit {
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
                            credit_inv.clone(),
                            &self.comp.graph(),
                            self.in_node.unwrap(),
                            self.out_node.unwrap(),
                        )
                } else {
                    complex
                        + complex_cycle_value_base(
                            credit_inv.clone(),
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
            .find(|(_i, super_node)| super_node.get_comp().contains(&node))
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
    pub last_hit: bool,
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

impl Display for CycleEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CycleEdge::Fixed(e) => write!(f, "{}", e),
            CycleEdge::Matching(e) => write!(f, "{}", e),
        }
    }
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
    pub fn all_outside_hits(&self) -> Vec<MatchingEdge> {
        self.non_path_matching_edges
            .iter()
            .filter(|e| e.hits_outside())
            .cloned()
            .collect_vec()
    }

    pub fn outside_hits_from(&self, node_idx: usize) -> Vec<MatchingEdge> {
        self.non_path_matching_edges
            .iter()
            .filter(|e| e.hits_outside() && e.source_path() == node_idx)
            .cloned()
            .collect_vec()
    }

    pub fn outside_edges_on(&self, node_idx: usize) -> Vec<Node> {
        self.non_path_matching_edges
            .iter()
            .filter(|e| e.hits_outside() && e.source_path() == node_idx)
            .map(|e| e.source())
            .collect_vec()
    }

    // Returns a list of nodes of node_idx which can have _one_ additional matching edge
    pub fn unmatched_nodes(&self, node_idx: usize) -> Vec<Node> {
        let comp = self.path[node_idx].get_comp();

        if let Component::Large(n) = comp {
            return vec![*n];
        }
        let fixed_incident = self.fixed_incident_edges(node_idx);
        let matching_sources = self
            .non_path_matching_edges
            .iter()
            .filter(|e| e.source_path() == node_idx)
            .map(|e| e.source())
            .collect_vec();

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

    pub fn nodes_with_fixed_edges(&self, node_idx: usize) -> Vec<Node> {
        let comp = self.path[node_idx].get_comp();
        let mut edge_endpoints = self
            .fixed_edge
            .iter()
            .flat_map(|e| comp.incident(e))
            .collect_vec();

        if let SuperNode::Zoomed(zoomed) = &self.path[node_idx] {
            if let Some(node) = zoomed.in_node {
                edge_endpoints.push(node)
            }
            if let Some(node) = zoomed.out_node {
                edge_endpoints.push(node)
            }
        }
        edge_endpoints
    }

    pub fn nodes_with_matching_edges(&self, node_idx: usize) -> Vec<Node> {
        self.non_path_matching_edges
            .iter()
            .filter(|e| e.source_path() == node_idx)
            .map(|e| e.source())
            .collect_vec()
    }

    pub fn nodes_with_edges(&self, node_idx: usize) -> Vec<Node> {
        let mut nodes = vec![
            self.nodes_with_matching_edges(node_idx),
            self.nodes_with_fixed_edges(node_idx),
        ]
        .concat();
        nodes.sort();
        nodes.dedup();
        nodes
    }


    pub fn nodes_without_edges(&self, node_idx: usize) -> Vec<Node> {
        let edge_endpoints = self.nodes_with_edges(node_idx);

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
        self.non_path_matching_edges
            .drain_filter(|e| e.source() == source && e.hits_path() == Some(hit_idx));

        self.fixed_edge.push(Edge(new_target, source));
    }

    pub fn fixed_incident_edges(&self, idx: usize) -> Vec<Edge> {
        let comp = self.path[idx].get_comp();

        self.fixed_edge
            .iter()
            .filter(|e| comp.is_incident(e))
            .cloned()
            .chain(
                vec![self.path_edge(idx), self.path_edge(idx + 1)]
                    .into_iter()
                    .flatten(),
            )
            .collect_vec()
    }

    pub fn path_edge(&self, idx: usize) -> Option<Edge> {
        if idx >= self.path.nodes.len() {
            return None;
        }
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
        let left_comp = self.path[left].get_comp();
        let right_comp = self.path[right].get_comp();
        let mut edges = self
            .fixed_edge
            .iter()
            .filter(|&edge| left_comp.is_incident(edge) && right_comp.is_incident(edge))
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
