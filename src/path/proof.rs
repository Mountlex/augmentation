use std::fmt::{Display, Write};
use std::ops::RangeBounds;
use std::path::PathBuf;

use itertools::Itertools;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

use crate::path::{PathComp, Pidx};
use crate::types::Edge;
use crate::Node;
use crate::{comps::Component, path::PathProofNode, CreditInv};

use super::enumerators::edges::edge_enumerator;
use super::enumerators::nice_pairs::nice_pairs_enumerator;
use super::enumerators::path_nodes::path_node_enumerator;
use super::enumerators::pseudo_cycles::enumerate_pseudo_cycles;
use super::enumerators::rearrangements::enumerate_rearrangements;
use super::tactics::contract::check_contractability;
use super::tactics::cycle_merge::check_cycle_merge;
use super::tactics::cycle_rearrange::check_path_rearrangement;
use super::tactics::local_merge::check_local_merge;
use super::tactics::longer_path::check_longer_nice_path;
use super::tactics::pendant_rewire::check_pendant_node;
use super::{
    InstPart, InstanceContext, InstanceProfile, MatchingEdge, MatchingEdgeId, NicePairConfig,
    PathNode, PseudoCycle, Rearrangement,
};

#[derive(Clone, Debug)]
enum StackElement {
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
pub struct Instance {
    stack: Vec<StackElement>,
    pub context: InstanceContext,
    pub matching_edge_id_counter: MatchingEdgeId,
}

impl Instance {
    fn push(&mut self, ele: StackElement) {
        self.stack.push(ele);
    }

    fn pop(&mut self) {
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
        self.inst_parts().flat_map(|part| part.good_edges.iter()).collect_vec()
    }

    pub fn good_out(&self) -> Vec<&Node> {
        self.inst_parts().flat_map(|part| part.good_out.iter()).collect_vec()
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

    #[allow(dead_code)]
    pub fn last_added_edges(&self) -> Vec<Edge> {
        let mut last_edges = vec![];
        for part in self.inst_parts() {
            if !part.edges.is_empty() {
                last_edges = part.edges.clone();
            }
            if !part.path_nodes.is_empty() {
                last_edges = vec![];
            }
            if !part.rem_edges.is_empty() {
                last_edges = vec![];
            }
        }
        last_edges
    }

    #[allow(dead_code)]
    fn last_added_rem_edges(&self) -> Vec<MatchingEdge> {
        let mut last_edges = vec![];
        for part in self.inst_parts() {
            if !part.edges.is_empty() {
                last_edges = part.rem_edges.clone();
            }
        }
        last_edges
    }

    pub fn rem_edges(&self) -> Vec<MatchingEdge> {
        let mut rem_edges: Vec<MatchingEdge> = vec![];
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

#[derive(Debug, Clone)]
enum Quantor {
    All(Enumerator, Box<Expression>, bool),
    AllOpt(OptEnumerator, Box<Expression>, Box<Expression>),
    Any(Enumerator, Box<Expression>),
}

impl Quantor {
    fn formula(&self) -> &Box<Expression> {
        match self {
            Quantor::All(_, t, _) => t,
            Quantor::AllOpt(_, t, _) => t,
            Quantor::Any(_, t) => t,
        }
    }

    fn prove(&self, stack: &mut Instance) -> PathProofNode {
        let mut enum_msg = String::new();
        let (cases, otherwise) = match self {
            Quantor::All(e, _, _sc) => (Some(e.get_iter(stack)), None),
            Quantor::Any(e, _) => (Some(e.get_iter(stack)), None),
            Quantor::AllOpt(e, _, otherwise) => {
                if let Some((cases, msg)) = e.try_iter(stack) {
                    enum_msg = msg;
                    (Some(cases), Some(otherwise))
                } else {
                    (None, Some(otherwise))
                }
            }
        };

        if let Some(cases) = cases {
            let mut proof = match self {
                Quantor::All(e, _, _) => PathProofNode::new_all(e.msg().to_string()),
                Quantor::AllOpt(e, _, _) => PathProofNode::new_all(e.msg().to_string()),
                Quantor::Any(e, _) => PathProofNode::new_any(e.msg().to_string()),
            };

            for instance in cases {
                let item_msg = format!("{} {}", instance, enum_msg);
                stack.push(instance);
                let mut proof_item = self.formula().prove(stack);
                proof_item = PathProofNode::new_info(item_msg, proof_item);
                let outcome = proof_item.eval();

                if let Quantor::All(Enumerator::PathNodes, _, _) = self {
                    proof_item.add_payload(stack.get_profile(outcome.success()));
                }

                proof.add_child(proof_item);
                let res = outcome.success();
                stack.pop();

                let should_break = match self {
                    Quantor::AllOpt(_, _, _) => !res,
                    Quantor::All(_, _, sc) => !res && *sc,
                    Quantor::Any(_, _) => res,
                };

                if should_break {
                    break;
                }
            }

            proof.eval();

            proof
        } else {
            otherwise.unwrap().prove(stack)
        }
    }
}

#[derive(Debug, Clone)]
enum Enumerator {
    PathNodes, // includes enumeration of in and out
    NicePairs,
    PseudoCycle,
    Rearrangments,
}

impl Enumerator {
    fn msg(&self) -> &str {
        match self {
            Enumerator::PathNodes => "Enumerate new path node",
            Enumerator::NicePairs => "Enumerate nice pairs",
            Enumerator::PseudoCycle => "Enumerate pseudo cycles",
            Enumerator::Rearrangments => "Enumerate rearrangements",
        }
    }

    fn get_iter(&self, stack: &mut Instance) -> Vec<StackElement> {
        match self {
            Enumerator::PathNodes => path_node_enumerator(stack)
                .map(StackElement::Inst)
                .collect_vec(),
            Enumerator::NicePairs => nice_pairs_enumerator(stack)
                .map(StackElement::Inst)
                .collect_vec(),
            Enumerator::PseudoCycle => enumerate_pseudo_cycles(stack)
                .map(StackElement::PseudoCycle)
                .collect_vec(),
            Enumerator::Rearrangments => enumerate_rearrangements(stack)
                .map(StackElement::Rearrangement)
                .collect_vec(),
        }
    }
}

#[derive(Debug, Clone)]
enum OptEnumerator {
    Edges,
}

impl OptEnumerator {
    fn msg(&self) -> &str {
        match self {
            OptEnumerator::Edges => "Enumerate edges",
        }
    }

    fn try_iter(&self, stack: &mut Instance) -> Option<(Vec<StackElement>, String)> {
        let result = match self {
            OptEnumerator::Edges => edge_enumerator(stack),
        };

        if let Some((case_iter, msg)) = result {
            Some((case_iter.map(StackElement::Inst).collect_vec(), msg))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
enum Tactic {
    LongerPath,
    CycleMerge,
    LocalMerge,
    Rearrangable,
    Contractable,
    Pendant,
    ManualCheck,
    TacticsExhausted,
    Print,
}

impl Tactic {
    fn prove(&self, stack: &mut Instance) -> PathProofNode {
        let proof = match self {
            Tactic::LongerPath => check_longer_nice_path(stack),
            Tactic::CycleMerge => check_cycle_merge(stack),
            Tactic::LocalMerge => check_local_merge(stack),
            Tactic::Rearrangable => check_path_rearrangement(stack),
            Tactic::Contractable => check_contractability(stack),
            Tactic::Pendant => check_pendant_node(stack),
            Tactic::ManualCheck => {
                let nodes = stack.path_nodes().collect_vec();

                if nodes.len() >= 3
                    && nodes[0].comp.is_c3()
                    && nodes[1].comp.is_c3()
                    && nodes[2].comp.is_c4()
                {
                    let all_edges = stack.all_edges();

                    let p2_in = nodes[2].in_node.unwrap();
                    let p2_conns = nodes[2].comp.nodes().iter().filter(|n| nodes[2].comp.is_adjacent(n, &p2_in)).cloned().collect_vec();

                    if all_edges.iter().filter(|e| e.path_incident(0.into()) && e.nodes_incident(&p2_conns)).count() > 1 && all_edges.iter().filter(|e| e.path_incident(1.into()) && e.nodes_incident(&p2_conns)).count() > 1 {
                        return PathProofNode::new_leaf("Manual proof for C3-C3-C4.".into(), true);
                    }

                }

                // if nodes.len() >= 3 && nodes[0].comp.is_c3() && nodes[1].comp.is_c6() {
                //     let relevant_edges = edges
                //         .iter()
                //         .filter(|e| e.between_path_nodes(1.into(), 2.into()));
                //     for e in relevant_edges {
                //         let c6_endpoint = e.endpoint_at(1.into()).unwrap();
                //         if outside.iter().any(|&o| npc.is_nice_pair(o, c6_endpoint)) {
                //             return PathProofNode::new_leaf(
                //                 "Manual proof for C3-C6: Better nice path found!".into(),
                //                 true,
                //             );
                //         }
                //     }
                // }

                // for c5 in nodes.iter().filter(|c| c.comp.is_c5()) {
                //     if !c5.path_idx.is_last()
                //         && edges.iter().all(|e| {
                //             !e.path_incident(c5.path_idx)
                //                 || (e.path_incident(c5.path_idx.succ().unwrap())
                //                     || e.path_incident(c5.path_idx.prec()))
                //         })
                //     {
                //         if outside.iter().filter(|n| c5.comp.contains(n)).count() >= 1 {
                //             return PathProofNode::new_leaf(
                //                 "Manual proof for in=out-C5: Better nice path found!".into(),
                //                 true,
                //             );
                //         }
                //     }
                // }

                // if nodes.len() >= 3
                //     && nodes[0].comp.is_c3()
                //     && nodes[1].comp.is_c6()
                //     && nodes[2].comp.is_c5()
                // {
                //     if rem_edges.iter().filter(|e| e.source_idx.is_last()).count() >= 2 {
                //         return PathProofNode::new_leaf(
                //             "Manual proof for C3-C6-C5 with double C3-REM!".into(),
                //             true,
                //         );
                //     }
                // }

                PathProofNode::new_leaf("No manual proof!".into(), false)
            }
            Tactic::TacticsExhausted => PathProofNode::new_leaf("Tactics exhausted!".into(), false),
            Tactic::Print => {
                let all_edges = stack.all_edges();
                let outside = stack.out_edges();
                let path_comps = stack.path_nodes().collect_vec();
                let rem_edges = stack.rem_edges();

                //  println!("{}", stack.get_profile(true));

                let msg = format!(
                    "Instance: [{}][{}][{}][{}]",
                    path_comps.iter().join(", "),
                    all_edges.iter().join(","),
                    outside.iter().join(","),
                    rem_edges.iter().join(",")
                );

                PathProofNode::new_leaf(msg, false)
            }
        };
        proof
    }
}

#[derive(Debug, Clone)]
enum Expression {
    Quantor(Quantor),
    Tactic(Tactic),
    Or(Box<Expression>, Box<Expression>),
}

impl Expression {
    fn prove(&self, stack: &mut Instance) -> PathProofNode {
        match self {
            Expression::Quantor(q) => q.prove(stack),
            Expression::Tactic(t) => t.prove(stack),
            Expression::Or(f1, f2) => {
                let mut proof1 = f1.prove(stack);
                proof1.eval();
                if proof1.success() {
                    proof1
                } else {
                    let proof2 = f2.prove(stack);
                    PathProofNode::new_or(proof1, proof2)
                }
            }
        }
    }
}

fn or(expr1: Expression, expr2: Expression) -> Expression {
    Expression::Or(Box::new(expr1), Box::new(expr2))
}

fn or3(expr1: Expression, expr2: Expression, expr3: Expression) -> Expression {
    or(expr1, or(expr2, expr3))
}

fn or4(expr1: Expression, expr2: Expression, expr3: Expression, expr4: Expression) -> Expression {
    or(expr1, or3(expr2, expr3, expr4))
}

fn or5(
    expr1: Expression,
    expr2: Expression,
    expr3: Expression,
    expr4: Expression,
    expr5: Expression,
) -> Expression {
    or(expr1, or4(expr2, expr3, expr4, expr5))
}

#[allow(dead_code)]
fn or6(
    expr1: Expression,
    expr2: Expression,
    expr3: Expression,
    expr4: Expression,
    expr5: Expression,
    expr6: Expression,
) -> Expression {
    or(expr1, or5(expr2, expr3, expr4, expr5, expr6))
}

fn expr(tactic: Tactic) -> Expression {
    Expression::Tactic(tactic)
}

fn all_sc(enumerator: Enumerator, expr: Expression) -> Expression {
    Expression::Quantor(Quantor::All(enumerator, Box::new(expr), true))
}

fn all(enumerator: Enumerator, expr: Expression, sc: bool) -> Expression {
    Expression::Quantor(Quantor::All(enumerator, Box::new(expr), sc))
}

fn all_opt(enumerator: OptEnumerator, expr: Expression, otherwise: Expression) -> Expression {
    Expression::Quantor(Quantor::AllOpt(
        enumerator,
        Box::new(expr),
        Box::new(otherwise),
    ))
}

fn any(enumerator: Enumerator, expr: Expression) -> Expression {
    Expression::Quantor(Quantor::Any(enumerator, Box::new(expr)))
}

fn inductive_proof(options: PathProofOptions, depth: u8) -> Expression {
    if depth > 0 {
        induction_step(options, inductive_proof(options, depth - 1))
    } else {
        or3(
            expr(Tactic::ManualCheck),
            expr(Tactic::Print),
            expr(Tactic::TacticsExhausted),
        )
    }
}

fn induction_step(options: PathProofOptions, step: Expression) -> Expression {
    all(
        Enumerator::PathNodes,
        all_sc(
            Enumerator::NicePairs,
            or4(
                expr(Tactic::Print),
                expr(Tactic::ManualCheck),
                progress(),
                find_all_edges(options.edge_depth, step),
            ),
        ),
        options.sc,
    )
}

fn find_all_edges(depth: u8, otherwise: Expression) -> Expression {
    if depth > 0 {
        find_edge(find_all_edges(depth - 1, otherwise.clone()), otherwise)
    } else {
        otherwise
    }
}

fn find_edge(enumerator: Expression, otherwise: Expression) -> Expression {
    all_opt(
        OptEnumerator::Edges,
        all_sc(Enumerator::NicePairs, or(progress(), enumerator)),
        otherwise,
    )
}

fn progress() -> Expression {
    or5(
        expr(Tactic::LocalMerge),
        expr(Tactic::Pendant),
        expr(Tactic::Contractable),
        expr(Tactic::LongerPath),
        any(
            Enumerator::PseudoCycle,
            or(
                expr(Tactic::CycleMerge),
                any(
                    Enumerator::Rearrangments,
                    or(expr(Tactic::Rearrangable), expr(Tactic::LongerPath)),
                ),
            ),
        ),
    )
}

pub fn check_progress(instance: &mut Instance, part: InstPart) -> bool {
    instance.push(StackElement::Inst(part));
    let mut proof = progress().prove(instance);
    proof.eval();
    let outcome = proof.outcome();
    instance.pop();
    outcome.success()
}

#[derive(Clone, Copy)]
pub struct PathProofOptions {
    pub edge_depth: u8,
    pub node_depth: u8,
    pub sc: bool,
}

pub fn prove_nice_path_progress(
    comps: Vec<Component>,
    last_comp: Component,
    credit_inv: &CreditInv,
    output_dir: PathBuf,
    output_depth: usize,
    options: PathProofOptions,
    parallel: bool,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    let nodes = comps
        .into_iter()
        .flat_map(|comp| {
            if comp.is_c5() {
                vec![PathNode::Unused(comp.clone()), PathNode::Used(comp)]
            } else {
                vec![PathNode::Unused(comp)]
            }
        })
        .collect_vec();

    let last_nodes = if last_comp.is_c5() {
        vec![
            PathNode::Unused(last_comp.clone()),
            PathNode::Used(last_comp),
        ]
    } else {
        vec![PathNode::Unused(last_comp)]
    };

    let proof_cases = last_nodes;

    if parallel {
        proof_cases.into_par_iter().for_each(|last_node| {
            prove_last_node(
                nodes.clone(),
                last_node,
                credit_inv.clone(),
                &output_dir,
                output_depth,
                options,
            )
        })
    } else {
        proof_cases.into_iter().for_each(|last_node| {
            prove_last_node(
                nodes.clone(),
                last_node,
                credit_inv.clone(),
                &output_dir,
                output_depth,
                options,
            )
        })
    };
}

fn prove_last_node(
    nodes: Vec<PathNode>,
    last_node: PathNode,
    credit_inv: CreditInv,
    output_dir: &PathBuf,
    output_depth: usize,
    options: PathProofOptions,
) {
    let comp = last_node.get_comp().clone();

    let mut proof = PathProofNode::new_all(format!("Proof of in_nodes of {}", comp.short_name()));
    let in_nodes = if comp.fixed_node().is_some() {
        vec![comp.fixed_node().unwrap()]
    } else {
        comp.matching_nodes().to_vec()
    };

    for in_node in in_nodes {
        let path_comp = PathComp {
            in_node: Some(in_node),
            out_node: None,
            comp: comp.clone(),
            used: last_node.is_used(),
            path_idx: Pidx::Last,
        };
        let mut instance = Instance {
            stack: vec![],
            context: InstanceContext {
                inv: credit_inv.clone(),
                comps: nodes.clone(),
            },
            matching_edge_id_counter: MatchingEdgeId(0),
        };
        instance.push(StackElement::Inst(InstPart::new_path_comp(path_comp)));

        let expr = inductive_proof(options, options.node_depth);
        let in_node_proof = expr.prove(&mut instance);
        proof.add_child(in_node_proof);
    }

    let outcome = proof.eval();

    print_path_statistics(&proof);
    let filename = if outcome.success() {
        println!(
            "✔️ Proved nice path progress ending in {}",
            last_node.short_name(),
        );
        output_dir.join(format!("proof_{}.txt", last_node.short_name(),))
    } else {
        println!(
            "❌ Disproved nice path progress ending in {}",
            last_node.short_name(),
        );
        output_dir.join(format!("wrong_proof_{}.txt", last_node.short_name(),))
    };

    println!();
    println!();

    let mut buf = String::new();
    writeln!(
        &mut buf,
        "============= Proof with {} ===============",
        credit_inv
    )
    .expect("Unable to write file");
    proof
        .print_tree(&mut buf, output_depth)
        .expect("Unable to format tree");
    std::fs::write(filename, buf).expect("Unable to write file");
}

fn print_path_statistics(proof: &PathProofNode) {
    let mut profiles = vec![];
    proof.get_payloads(&mut profiles);
    let mut profiles = profiles.into_iter().unique().collect_vec();

    let p_copy = profiles.clone();

    profiles.drain_filter(|p| {
        p.success
            && p_copy
                .iter()
                .any(|p2| p.comp_types == p2.comp_types && !p2.success)
    });
    profiles.drain_filter(|p| !p.success);

    let p_copy = profiles.clone();
    profiles.drain_filter(|p| p_copy.iter().any(|p2| p2.includes(p)));

    for profile in profiles {
        println!("{}", profile);
    }
}
