use std::fmt::{Display, Write};
use std::path::PathBuf;

use itertools::Itertools;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

use crate::path::instance::{InstanceContext, PathNode};
use crate::path::{PathComp, Pidx};
use crate::types::Edge;
use crate::Node;
use crate::{comps::Component, path::PathProofNode, CreditInv};

use super::enumerators::edges::edge_enumerator;
use super::enumerators::nice_pairs::nice_pairs_enumerator;
use super::enumerators::path_nodes::{path_comp_enumerator, path_extension_enumerator};
use super::enumerators::pseudo_cycles::enumerate_pseudo_cycles;
use super::enumerators::rearrangements::enumerate_rearrangements;
use super::instance::{Instance, StackElement};
use super::tactics::contract::check_contractability;
use super::tactics::cycle_merge::check_cycle_merge;
use super::tactics::cycle_rearrange::check_path_rearrangement;
use super::tactics::local_merge::check_local_merge;
use super::tactics::longer_path::check_longer_nice_path;
use super::tactics::pendant_rewire::check_pendant_node;
use super::{EdgeId, HalfAbstractEdge};

#[derive(Clone, Debug)]
pub struct InstPart {
    pub path_nodes: Vec<PathComp>,
    pub nice_pairs: Vec<(Node, Node)>,
    pub edges: Vec<Edge>,
    pub out_edges: Vec<Node>,
    pub used_for_credit_gain: Vec<Node>,
    pub rem_edges: Vec<HalfAbstractEdge>,
    pub non_rem_edges: Vec<EdgeId>,
    pub connected_nodes: Vec<Node>,
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
            connected_nodes: vec![],
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
            && self.connected_nodes.is_empty()
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
            connected_nodes: vec![],
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

#[derive(Debug, Clone)]
enum Quantor {
    All(Enumerator, Box<Expression>, bool),
    AllOpt(OptEnumerator, Box<Expression>, Box<Expression>, bool),
    Any(Enumerator, Box<Expression>),
}

impl Quantor {
    fn formula(&self) -> &Box<Expression> {
        match self {
            Quantor::All(_, t, _) => t,
            Quantor::AllOpt(_, t, _, _) => t,
            Quantor::Any(_, t) => t,
        }
    }

    fn prove(&self, stack: &mut Instance) -> PathProofNode {
        let mut enum_msg = String::new();
        let (case_iterator, otherwise) = match self {
            Quantor::All(e, _, _sc) => (Some(e.get_iter(stack)), None),
            Quantor::Any(e, _) => (Some(e.get_iter(stack)), None),
            Quantor::AllOpt(e, _, otherwise, _) => {
                if let Some((cases, msg)) = e.try_iter(stack) {
                    enum_msg = msg;
                    (Some(cases), Some(otherwise))
                } else {
                    (None, Some(otherwise))
                }
                //(None, Some(otherwise))
            }
        };

        if let Some(case_iterator) = case_iterator {
            let mut proof = match self {
                Quantor::All(e, _, _) => PathProofNode::new_all(e.msg().to_string()),
                Quantor::AllOpt(e, _, _, _) => PathProofNode::new_all(e.msg().to_string()),
                Quantor::Any(e, _) => PathProofNode::new_any(e.msg().to_string()),
            };

            //if false {
            if let Quantor::AllOpt(OptEnumerator::PathNode, _, _, _) = self {
                let cases = case_iterator.collect_vec();
                let nodes: Vec<PathProofNode> = cases
                    .into_par_iter()
                    .map(|case| {
                        let item_msg = match case {
                            StackElement::Inst(_) => format!("part {}", enum_msg),
                            StackElement::PseudoCycle(_) => format!("pc {}", enum_msg),
                            StackElement::Rearrangement(_) => format!("rearr {}", enum_msg),
                        };
                        let mut stack = stack.clone();
                        stack.push(case);
                        let mut proof_item = self.formula().prove(&mut stack);
                        proof_item = PathProofNode::new_info(item_msg, proof_item);
                        let outcome = proof_item.eval();

                        if let Quantor::AllOpt(OptEnumerator::PathNode, _, _, _) = self {
                            proof_item.add_payload(stack.get_profile(outcome.success()));
                        }

                        proof_item
                    })
                    .collect();
                for node in nodes {
                    proof.add_child(node);
                }
            } else {
                for case in case_iterator {
                    let item_msg = match case {
                        StackElement::Inst(_) => format!("part {}", enum_msg),
                        StackElement::PseudoCycle(_) => format!("pc {}", enum_msg),
                        StackElement::Rearrangement(_) => format!("rearr {}", enum_msg),
                    };
                    stack.push(case);
                    let mut proof_item = self.formula().prove(stack);
                    proof_item = PathProofNode::new_info(item_msg, proof_item);
                    let outcome = proof_item.eval();

                    if let Quantor::AllOpt(OptEnumerator::PathNode, _, _, _) = self {
                        proof_item.add_payload(stack.get_profile(outcome.success()));
                    }

                    proof.add_child(proof_item);
                    let res = outcome.success();
                    stack.pop();

                    let should_break = match self {
                        Quantor::AllOpt(_, _, _, sc) => !res && *sc,
                        Quantor::All(_, _, sc) => !res && *sc,
                        Quantor::Any(_, _) => res,
                    };

                    if should_break {
                        break;
                    }
                }
            }

            proof.eval_and_prune();

            proof
        } else {
            otherwise.unwrap().prove(stack)
        }
    }
}

#[derive(Debug, Clone)]
enum Enumerator {
    NicePairs,
    PseudoCycle(bool),
    Rearrangments(bool),
}

impl Enumerator {
    fn msg(&self) -> &str {
        match self {
            //Enumerator::PathNodes => "Enumerate new path node",
            Enumerator::NicePairs => "Enumerate nice pairs",
            Enumerator::PseudoCycle(_) => "Enumerate pseudo cycles",
            Enumerator::Rearrangments(_) => "Enumerate rearrangements",
        }
    }

    fn get_iter(&self, stack: &Instance) -> Box<dyn Iterator<Item = StackElement>> {
        match self {
            // Enumerator::PathNodes => {
            //     Box::new(path_extension_enumerator(stack).map(StackElement::Inst))
            // }
            Enumerator::NicePairs => Box::new(nice_pairs_enumerator(stack).map(StackElement::Inst)),

            Enumerator::PseudoCycle(finite) => {
                Box::new(enumerate_pseudo_cycles(stack, *finite).map(StackElement::PseudoCycle))
            }

            Enumerator::Rearrangments(finite) => {
                Box::new(enumerate_rearrangements(stack, *finite).map(StackElement::Rearrangement))
            }
        }
    }
}

#[derive(Debug, Clone)]
enum OptEnumerator {
    Edges(bool),
    PathNode,
}

impl OptEnumerator {
    fn msg(&self) -> &str {
        match self {
            OptEnumerator::Edges(_) => "Enumerate edges",
            OptEnumerator::PathNode => "Enumerate path node",
        }
    }

    fn try_iter(
        &self,
        instance: &mut Instance,
    ) -> Option<(Box<dyn Iterator<Item = StackElement>>, String)> {
        let result = match self {
            OptEnumerator::Edges(finite) => edge_enumerator(instance, *finite),
            OptEnumerator::PathNode => path_extension_enumerator(instance),
        };

        if let Some((case_iter, msg)) = result {
            Some((Box::new(case_iter.map(StackElement::Inst)), msg))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone)]
enum Tactic {
    LongerPath(bool),
    CycleMerge,
    LocalMerge,
    Rearrangable(bool),
    Contractable,
    Pendant,
    TacticsExhausted(bool),
    Print,
}

impl Tactic {
    fn prove(&self, stack: &mut Instance) -> PathProofNode {
        let proof = match self {
            Tactic::LongerPath(finite) => check_longer_nice_path(stack, *finite),
            Tactic::CycleMerge => check_cycle_merge(stack),
            Tactic::LocalMerge => check_local_merge(stack),
            Tactic::Rearrangable(finite) => check_path_rearrangement(stack, *finite),
            Tactic::Contractable => check_contractability(stack),
            Tactic::Pendant => check_pendant_node(stack),
            // Tactic::FilterInfinite => {
            //     let rem_edges = stack.rem_edges();
            //     if rem_edges.len() > 0 {
            //         PathProofNode::new_leaf("Infinite instance is true".into(), true)
            //     } else {
            //         PathProofNode::new_leaf("Finite instance to be checked.".into(), false)
            //     }
            // }
            Tactic::TacticsExhausted(finite) => {
                if *finite {
                    log::info!("tactics (finite) exhausted for: {}", stack);
                    PathProofNode::new_leaf("Tactics (finite) exhausted!".into(), false)
                } else {
                    log::info!("tactics exhausted for: {}", stack);
                    PathProofNode::new_leaf("Tactics exhausted!".into(), false)
                }
            }
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
    And(Box<Expression>, Box<Expression>),
    Map(Mapper, Box<Expression>),
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
            Expression::And(f1, f2) => {
                let mut proof1 = f1.prove(stack);
                proof1.eval();
                if !proof1.success() {
                    proof1
                } else {
                    let proof2 = f2.prove(stack);
                    PathProofNode::new_and(proof1, proof2)
                }
            }
            Expression::Map(mapper, expression) => {
                let element = mapper.stack_element(&stack);
                stack.push(element);
                let result = expression.prove(stack);
                stack.pop();
                return result
            }
        }
    }
}

fn map(mapper: Mapper, expr: Expression) -> Expression {
    Expression::Map(mapper, Box::new(expr))
}

#[derive(Clone, Debug)]
enum Mapper {
    ToFiniteInstance,
}

impl Mapper {
    fn stack_element(&self, stack: &Instance) -> StackElement {
        match self {
            Mapper::ToFiniteInstance => {
                let mut rem_ids = stack.rem_edges().iter().map(|e| e.id).collect_vec();
                let mut rem_sources = stack.rem_edges().iter().map(|e| e.source).collect_vec();

                let mut part = InstPart::empty();
                part.non_rem_edges.append(&mut rem_ids);
                part.out_edges.append(&mut rem_sources);

               StackElement::Inst(part)
            }
        }
    }
}

fn and(expr1: Expression, expr2: Expression) -> Expression {
    Expression::And(Box::new(expr1), Box::new(expr2))
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

// fn all(enumerator: Enumerator, expr: Expression, sc: bool) -> Expression {
//     Expression::Quantor(Quantor::All(enumerator, Box::new(expr), sc))
// }

fn all_opt(
    enumerator: OptEnumerator,
    expr: Expression,
    otherwise: Expression,
    sc: bool,
) -> Expression {
    Expression::Quantor(Quantor::AllOpt(
        enumerator,
        Box::new(expr),
        Box::new(otherwise),
        sc,
    ))
}

fn any(enumerator: Enumerator, expr: Expression) -> Expression {
    Expression::Quantor(Quantor::Any(enumerator, Box::new(expr)))
}

fn inductive_proof(options: PathProofOptions, depth: u8) -> Expression {
    if depth > 0 {
        induction_step(options, inductive_proof(options, depth - 1))
    } else {
        or(expr(Tactic::Print), expr(Tactic::TacticsExhausted(false)))
    }
}

fn induction_step(options: PathProofOptions, step: Expression) -> Expression {
    // and(
    //     // finite case
    //     map(
    //         Mapper::ToFiniteInstance,
    //         or3(
    //             expr(Tactic::Print),
    //             //expr(Tactic::FilterInfinite),
    //             progress(true),
    //             find_all_edges_and_progress(
    //                 options.edge_depth,
    //                 true,
    //                 or(expr(Tactic::Print), expr(Tactic::TacticsExhausted(true))),
    //             ),
    //         ),
    //     ), // infinite case
        all_opt(
            OptEnumerator::PathNode,
            all_sc(
                Enumerator::NicePairs,
                or3(
                    expr(Tactic::Print),
                    progress(false),
                    find_all_edges_and_progress(options.edge_depth, false, step),
                ),
            ),
            or(expr(Tactic::Print), expr(Tactic::TacticsExhausted(false))),
            options.sc,
    //    ),
    )
}

fn find_all_edges_and_progress(depth: u8, finite: bool, otherwise: Expression) -> Expression {
    if depth > 0 {
        find_edge_and_progress(
            find_all_edges_and_progress(depth - 1, finite, otherwise.clone()),
            finite,
            otherwise,
        )
    } else {
        otherwise
    }
}

fn find_edge_and_progress(
    enumerator: Expression,
    finite: bool,
    otherwise: Expression,
) -> Expression {
    all_opt(
        OptEnumerator::Edges(finite),
        all_sc(Enumerator::NicePairs, or(progress(finite), enumerator)),
        otherwise,
        true,
    )
}

fn progress(finite: bool) -> Expression {
    or5(
        expr(Tactic::LocalMerge),
        expr(Tactic::Pendant),
        expr(Tactic::Contractable),
        expr(Tactic::LongerPath(finite)),
        any(
            Enumerator::PseudoCycle(finite),
            or(
                expr(Tactic::CycleMerge),
                any(
                    Enumerator::Rearrangments(finite),
                    or(
                        expr(Tactic::Rearrangable(finite)),
                        expr(Tactic::LongerPath(finite)),
                    ),
                ),
            ),
        ),
    )
}

pub fn check_progress(instance: &mut Instance, finite: bool, part: InstPart) -> bool {
    instance.push(StackElement::Inst(part));
    let mut proof = progress(finite).prove(instance);
    proof.eval();
    let outcome = proof.outcome();
    instance.pop();
    outcome.success()
}

#[derive(Clone, Copy)]
pub struct PathProofOptions {
    pub edge_depth: u8,
    pub node_depth: u8,
    pub initial_depth: u8,
    pub sc: bool,
}

pub fn prove_nice_path_progress(
    comps: Vec<Component>,
    last_comp: Component,
    credit_inv: &CreditInv,
    output_dir: PathBuf,
    output_depth: usize,
    options: PathProofOptions,
    _parallel: bool,
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

    proof_cases.into_iter().for_each(|last_node| {
        prove_last_node(
            nodes.clone(),
            last_node,
            credit_inv.clone(),
            &output_dir,
            output_depth,
            options,
            true,
        )
    })
}

fn compute_initial_cases(
    nodes: Vec<PathNode>,
    last_node: PathNode,
    mut depth: u8,
    credit_inv: CreditInv,
) -> Vec<Instance> {
    let comp = last_node.get_comp().clone();

    let in_nodes = if comp.fixed_node().is_some() {
        vec![comp.fixed_node().unwrap()]
    } else {
        comp.matching_nodes().to_vec()
    };

    let mut cases = in_nodes
        .into_iter()
        .map(|in_node| {
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
            };
            instance.push(StackElement::Inst(InstPart::new_path_comp(path_comp)));

            instance
        })
        .collect_vec();

    while depth > 1 {
        cases = cases
            .into_iter()
            .flat_map(|instance| {
                let parts = path_comp_enumerator(&instance).collect_vec();
                parts.into_iter().map(move |part| {
                    let mut instance = instance.clone();
                    instance.push(StackElement::Inst(part));
                    instance
                })
            })
            .collect_vec();

        depth -= 1;
    }

    cases
}

use chrono::prelude::*;

fn prove_last_node(
    nodes: Vec<PathNode>,
    last_node: PathNode,
    credit_inv: CreditInv,
    output_dir: &PathBuf,
    output_depth: usize,
    options: PathProofOptions,
    _parallel: bool,
) {
    let cases = compute_initial_cases(
        nodes,
        last_node.clone(),
        options.initial_depth,
        credit_inv.clone(),
    );
    println!("{} cases to check!", cases.len());

    for case in &cases {
        let profile = case.get_profile(false);
        println!("{}: {}", profile, case);
    }

    let mut total_proof = PathProofNode::new_all("Full proof".to_string());

    let proofs: Vec<PathProofNode> = cases
        .into_par_iter()
        .map(|mut case| {
            let expr = inductive_proof(options, options.node_depth);
            let mut proof = expr.prove(&mut case);
            let outcome = proof.eval();
            let profile = case.get_profile(outcome.success());

            let local: String = Local::now().format("%Y-%m-%d %H:%M:%S").to_string();
            if outcome.success() {
                println!("[{}] ✔️ Proved case {}: {}", local, profile, case);
            } else {
                println!("[{}] ❌ Disproved case {}: {}", local, profile, case);
                let buf = proof_to_string(&proof, output_depth, &credit_inv);
                log::info!("{}", buf);
            };

            proof
        })
        .collect();

    for p in proofs {
        total_proof.add_child(p);
    }

    total_proof.eval();
    let outcome = total_proof.outcome();
    //print_path_statistics(&total_proof);
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

    let buf = proof_to_string(&total_proof, output_depth, &credit_inv);
    std::fs::write(filename, buf).expect("Unable to write file");
}

fn proof_to_string(proof: &PathProofNode, output_depth: usize, credit_inv: &CreditInv) -> String {
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
    buf
}

#[allow(dead_code)]
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
