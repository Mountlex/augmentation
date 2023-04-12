use std::fmt::Display;

use itertools::Itertools;

use crate::{
    comps::{CompType, Component},
    types::Edge,
    Credit, CreditInv, Node,
};

use super::{proof::InstPart, HalfAbstractEdge, NicePairConfig, PathComp, Pidx};

#[derive(Clone, Debug)]
pub struct Instance {
    pub stack: Vec<StackElement>,
    pub context: InstanceContext,
}

impl Instance {
    pub fn push(&mut self, ele: StackElement) {
        self.stack.push(ele);
    }

    pub fn pop(&mut self) {
        self.stack.pop().unwrap();
    }

    pub fn top_mut(&mut self) -> Option<&mut InstPart> {
        self.stack.last_mut().and_then(|last| match last {
            StackElement::Inst(part) => Some(part),
            StackElement::PseudoCycle(_) => None,
            StackElement::Rearrangement(_) => None,
        })
    }

    pub fn inst_parts(&self) -> impl Iterator<Item = &'_ InstPart> {
        self.stack.iter().flat_map(|ele| ele.as_inst_part())
    }

    #[allow(dead_code)]
    fn nice_pairs(&self) -> impl Iterator<Item = &'_ (Node, Node)> {
        self.inst_parts().flat_map(|part| part.nice_pairs.iter())
    }

    pub fn out_edges(&self) -> Vec<Node> {
        self.inst_parts()
            .flat_map(|part| part.out_edges.iter())
            .cloned()
            .collect_vec()
    }

    pub fn npc(&self) -> NicePairConfig {
        let tuples = self
            .inst_parts()
            .flat_map(|part| part.nice_pairs.iter())
            .unique()
            .cloned()
            .collect_vec();
        NicePairConfig { nice_pairs: tuples }
    }

    fn implied_edges(&self) -> impl Iterator<Item = &'_ Edge> {
        self.inst_parts().flat_map(|part| part.edges.iter())
    }

    pub fn good_edges(&self) -> Vec<&Edge> {
        self.inst_parts()
            .flat_map(|part| part.good_edges.iter())
            .collect_vec()
    }

    pub fn good_out(&self) -> Vec<&Node> {
        self.inst_parts()
            .flat_map(|part| part.good_out.iter())
            .collect_vec()
    }

    pub fn all_edges(&self) -> Vec<Edge> {
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

    pub fn last_single_edge(&self) -> Option<Edge> {
        self.inst_parts().last().and_then(|part| {
            if part.edges.len() == 1 {
                part.edges.first().cloned()
            } else {
                None
            }
        })
    }

    pub fn rem_edges(&self) -> Vec<HalfAbstractEdge> {
        let mut rem_edges: Vec<HalfAbstractEdge> = vec![];
        for part in self.inst_parts() {
            if !part.non_rem_edges.is_empty() {
                for non_rem in &part.non_rem_edges {
                    if let Some((pos, _)) = rem_edges
                        .iter()
                        .find_position(|edge| &edge.source == non_rem)
                    {
                        rem_edges.swap_remove(pos);
                    }
                }
            }
            rem_edges.append(&mut part.rem_edges.iter().cloned().collect_vec());
        }

        rem_edges
    }

    pub fn pseudo_cycle(&self) -> Option<&PseudoCycle> {
        if let Some(StackElement::PseudoCycle(pc)) = self.stack.last() {
            Some(pc)
        } else {
            None
        }
    }

    pub fn rearrangement(&self) -> Option<&Rearrangement> {
        if let Some(StackElement::Rearrangement(pc)) = self.stack.last() {
            Some(pc)
        } else {
            None
        }
    }

    pub fn component_edges(&self) -> impl Iterator<Item = Edge> + '_ {
        self.path_nodes().flat_map(|c| {
            c.comp
                .edges()
                .into_iter()
                .map(|(u, v)| Edge::new(u, c.path_idx, v, c.path_idx))
        })
    }

    pub fn get_profile(&self, success: bool) -> InstanceProfile {
        let comps = self.path_nodes().map(|n| n.comp.comp_type()).collect_vec();
        InstanceProfile {
            comp_types: comps,
            success,
        }
    }

    pub fn path_nodes(&self) -> impl Iterator<Item = &'_ PathComp> {
        self.inst_parts().flat_map(|part| part.path_nodes.iter())
    }

    pub fn connected_nodes(&self) -> impl Iterator<Item = &'_ Node> {
        self.inst_parts()
            .flat_map(|part| part.connected_nodes.iter())
    }
}

#[derive(Clone, Debug)]
pub enum StackElement {
    Inst(InstPart),
    PseudoCycle(PseudoCycle),
    Rearrangement(Rearrangement),
}

impl StackElement {
    fn as_inst_part(&self) -> Option<&InstPart> {
        match self {
            StackElement::Inst(inst) => Some(inst),
            _ => None,
        }
    }
}

impl Display for StackElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StackElement::Inst(part) => write!(f, "{}", part),
            StackElement::PseudoCycle(part) => write!(f, "{}", part),
            StackElement::Rearrangement(part) => write!(f, "{}", part),
        }
    }
}

impl Display for Instance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut path_comps = self.path_nodes();
        let all_edges = self.all_edges();
        let outside = self.out_edges();
        let rem_edges = self.rem_edges();
        write!(
            f,
            "Instance: [{}] E=[{}] O=[{}] R=[{}]",
            path_comps.join(", "),
            all_edges.iter().join(","),
            outside.iter().join(","),
            rem_edges.iter().join(",")
        )
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

    pub fn short_name(&self) -> String {
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
    pub total_edge_cost: Credit,
}

impl PseudoCycle {
    pub fn consecutive_end(&self) -> bool {
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
                CycleComp::Rem => "REM".to_string(),
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
        write!(f, "{}", self.comp_types.iter().join("--"))
    }
}
