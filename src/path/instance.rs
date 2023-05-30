use std::fmt::Display;

use itertools::Itertools;

use crate::{
    comps::{CompType, Component},
    types::Edge,
    Credit, CreditInv, Node,
};

use super::{
    extension::Extension,  pseudo_cycle::PseudoCycle, EdgeId, HalfAbstractEdge,
    NicePairConfig, PathComp, Pidx, logic::InstanceTrait,
};

#[derive(Clone, Debug)]
pub struct InstPart {
    pub path_nodes: Vec<PathComp>,
    pub nice_pairs: Vec<(Node, Node)>,
    pub edges: Vec<Edge>,
    pub out_edges: Vec<Node>,
    pub used_for_credit_gain: Vec<Node>,
    pub rem_edges: Vec<HalfAbstractEdge>,
    pub non_rem_edges: Vec<EdgeId>,
    pub contractability_checked: Vec<Pidx>,
    pub good_edges: Vec<Edge>,
    pub good_out: Vec<Node>,
}

impl InstPart {
    pub fn empty() -> InstPart {
        InstPart {
            path_nodes: vec![],
            nice_pairs: vec![],
            edges: vec![],
            out_edges: vec![],
            rem_edges: vec![],
            used_for_credit_gain: vec![],
            non_rem_edges: vec![],
            contractability_checked: vec![],
            good_edges: vec![],
            good_out: vec![],
        }
    }

    pub fn is_empty(&self) -> bool {
        self.path_nodes.is_empty()
            && self.nice_pairs.is_empty()
            && self.edges.is_empty()
            && self.out_edges.is_empty()
            && self.used_for_credit_gain.is_empty()
            && self.rem_edges.is_empty()
            && self.non_rem_edges.is_empty()
            && self.contractability_checked.is_empty()
            && self.good_edges.is_empty()
            && self.good_out.is_empty()
    }

    pub fn new_path_comp(path_comp: PathComp) -> InstPart {
        InstPart {
            path_nodes: vec![path_comp],
            nice_pairs: vec![],
            edges: vec![],
            out_edges: vec![],
            used_for_credit_gain: vec![],
            rem_edges: vec![],
            non_rem_edges: vec![],
            contractability_checked: vec![],
            good_edges: vec![],
            good_out: vec![],
        }
    }

    pub fn new_nice_pairs(nice_pairs: Vec<(Node, Node)>) -> InstPart {
        InstPart {
            path_nodes: vec![],
            nice_pairs,
            edges: vec![],
            out_edges: vec![],
            used_for_credit_gain: vec![],
            rem_edges: vec![],
            non_rem_edges: vec![],
            contractability_checked: vec![],
            good_edges: vec![],
            good_out: vec![],
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
        if !self.used_for_credit_gain.is_empty() {
            write!(f, "Used for credit gain: ")?;
            write!(f, "{}", self.used_for_credit_gain.iter().join(", "))?;
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
pub struct Instance {
    pub stack: Vec<StackElement>,
    pub context: InstanceContext,
}

impl InstanceTrait for Instance {
    type StackElement = StackElement;

    fn item_msg(&self, item: &Self::StackElement, enum_msg: &str) -> String {
        match item {
                        StackElement::Inst(_) => format!("part {}", enum_msg),
                        StackElement::PseudoCycle(_) => format!("pc {}", enum_msg),
                        StackElement::Rearrangement(_) => format!("rearr {}", enum_msg),
                    }
    }

    fn push(&mut self, ele: StackElement) {
        self.stack.push(ele);
    }

    fn pop(&mut self) {
        self.stack.pop().unwrap();
    }
}

impl Instance {
    

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
        // TODO
        let nice_pairs = self
            .inst_parts()
            .flat_map(|part| {
                let initial_nps = part
                    .path_nodes
                    .iter()
                    .flat_map(|c| c.initial_nps.clone())
                    .collect_vec();
                vec![initial_nps, part.nice_pairs.clone()].concat()
            })
            .collect_vec();
        NicePairConfig { nice_pairs }
        // if let Some(part) = self
        //     .inst_parts()
        //     .filter(|part| !part.nice_pairs.is_empty())
        //     .last()
        // {
        //     NicePairConfig {
        //         nice_pairs: part.nice_pairs.clone(),
        //     }
        // } else {
        //     NicePairConfig::empty()
        // }
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

    pub fn used_for_credit_gain(&self) -> Vec<Node> {
        self.inst_parts()
            .flat_map(|part| part.used_for_credit_gain.iter())
            .cloned()
            .collect_vec()
    }

    pub fn all_edges(&self) -> Vec<Edge> {
        let mut implied_edges = self.implied_edges().cloned().collect_vec();

        let cheap_edges = implied_edges
            .iter()
            .filter(|e| e.cost < Credit::from_integer(1))
            .cloned()
            .collect_vec();
        if !cheap_edges.is_empty() {
            implied_edges.drain_filter(|e| {
                cheap_edges.iter().any(|e2| {
                    e.cost > e2.cost && e2.node_incident(&e.n1) && e2.node_incident(&e.n2)
                })
            });
        }

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

    // pub fn last_single_edge(&self) -> Option<Edge> {
    //     //sh run2_7.sh  25,08s user 0,19s system 146% cpu 17,255 total
    //     return None;
    //     let parts = self.inst_parts().collect_vec();

    //     let mut lookback = 1;

    //     while lookback <= parts.len() {
    //         if parts[parts.len() - lookback].edges.len() == 1 {
    //             return parts[parts.len() - lookback].edges.first().cloned();
    //         } else if parts[parts.len() - lookback].edges.len() > 1 {
    //             break;
    //         } else if !parts[parts.len() - lookback].path_nodes.is_empty() {
    //             break;
    //         } else if !parts[parts.len() - lookback].out_edges.is_empty() {
    //             break;
    //         } else if !parts[parts.len() - lookback].rem_edges.is_empty() {
    //             break;
    //         }
    //         lookback += 1;
    //     }

    //     None
    // }

    pub fn rem_edges(&self) -> Vec<HalfAbstractEdge> {
        let rem_edges: Vec<HalfAbstractEdge> = self
            .inst_parts()
            .flat_map(|part| part.rem_edges.iter())
            .cloned()
            .collect_vec();

        let non_rem_edges: Vec<EdgeId> = self
            .inst_parts()
            .flat_map(|part| part.non_rem_edges.iter())
            .cloned()
            .collect_vec();

        rem_edges
            .into_iter()
            .filter(|e| !non_rem_edges.contains(&e.id))
            .collect_vec()
    }

    pub fn new_rem_id(&self) -> EdgeId {
        let rem_edges: EdgeId = self
            .inst_parts()
            .flat_map(|part| part.rem_edges.iter())
            .map(|e| e.id)
            .max()
            .unwrap_or(EdgeId(0));

        let non_rem_edges: EdgeId = self
            .inst_parts()
            .flat_map(|part| part.non_rem_edges.iter())
            .cloned()
            .max()
            .unwrap_or(EdgeId(0));

        non_rem_edges.max(rem_edges).inc()
    }

    pub fn pseudo_cycle(&self) -> Option<&PseudoCycle> {
        if let Some(StackElement::PseudoCycle(pc)) = self.stack.last() {
            Some(pc)
        } else {
            None
        }
    }

    pub fn rearrangement(&self) -> Option<&Extension> {
        if let Some(StackElement::Rearrangement(pc)) = self.stack.last() {
            Some(pc)
        } else {
            None
        }
    }

    // pub fn component_edges(&self) -> impl Iterator<Item = Edge> + '_ {
    //     self.path_nodes().flat_map(|c| {
    //         c.comp
    //             .edges()
    //             .into_iter()
    //             .map(|(u, v)| Edge::new(u, c.path_idx, v, c.path_idx))
    //     })
    // }

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

    pub fn contractability_checked(&self) -> impl Iterator<Item = &'_ Pidx> {
        self.inst_parts()
            .flat_map(|part| part.contractability_checked.iter())
    }
}

#[derive(Clone, Debug)]
pub enum StackElement {
    Inst(InstPart),
    PseudoCycle(PseudoCycle),
    Rearrangement(Extension),
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
        let added_np = self
            .stack
            .iter()
            .flat_map(|part| part.as_inst_part())
            .flat_map(|part| part.nice_pairs.clone())
            .collect_vec();
        write!(
            f,
            "Instance: [{}] E=[{}] O=[{}] R=[{}] NP=[{}]",
            path_comps.join(", "),
            all_edges.iter().join(","),
            outside.iter().join(","),
            rem_edges.iter().join(","),
            added_np
                .iter()
                .map(|(u, v)| format!("({},{})", u, v))
                .join(","),
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
    #[allow(dead_code)]
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
