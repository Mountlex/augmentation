use std::fmt::{Display, Write};
use std::path::PathBuf;

use itertools::Itertools;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

use crate::path::{PathComp, Pidx};
use crate::types::Edge;
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
use super::{InstPart, InstanceContext, MatchingEdgeId, PathNode, PseudoCycle, Rearrangement};

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
        let mut outside = self.out_edges();
        let rem_edges = self.rem_edges();
        write!(
            f,
            "Instance: [{}][{}][{}][{}]",
            path_comps.join(", "),
            all_edges.iter().join(","),
            outside.join(","),
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
        self.stack.pop();
    }

    pub fn inst_parts<'a>(&'a self) -> impl Iterator<Item = &'a InstPart> {
        self.stack.iter().flat_map(|ele| ele.as_inst_part())
    }

    pub fn pseudo_cycle<'a>(&'a self) -> Option<&'a PseudoCycle> {
        if let Some(StackElement::PseudoCycle(pc)) = self.stack.last() {
            Some(pc)
        } else {
            None
        }
    }

    pub fn rearrangement<'a>(&'a self) -> Option<&'a Rearrangement> {
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
            Quantor::All(e, _, sc) => (Some(e.get_iter(stack)), None),
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
                .map(|part| StackElement::Inst(part))
                .collect_vec(),
            Enumerator::NicePairs => nice_pairs_enumerator(stack)
                .map(|part| StackElement::Inst(part))
                .collect_vec(),
            Enumerator::PseudoCycle => enumerate_pseudo_cycles(stack)
                .map(|part| StackElement::PseudoCycle(part))
                .collect_vec(),
            Enumerator::Rearrangments => enumerate_rearrangements(stack)
                .map(|part| StackElement::Rearrangement(part))
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
            Some((
                case_iter.map(|part| StackElement::Inst(part)).collect_vec(),
                msg,
            ))
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
    FiniteInstance,
    TacticsExhausted,
    Print,
}

impl Tactic {
    fn prove(&self, stack: &Instance) -> PathProofNode {
        let proof = match self {
            Tactic::LongerPath => check_longer_nice_path(stack),
            Tactic::CycleMerge => check_cycle_merge(stack),
            Tactic::LocalMerge => check_local_merge(stack),
            Tactic::Rearrangable => check_path_rearrangement(stack),
            Tactic::Contractable => check_contractability(stack),
            Tactic::Pendant => check_pendant_node(stack),
            Tactic::FiniteInstance => todo!(),
            Tactic::ManualCheck => {
                let nodes = stack.path_nodes().collect_vec();
                let outside = stack.out_edges().collect_vec();
                let rem_edges = stack.rem_edges();
                let edges = stack.all_edges();
                let npc = stack.npc();


               if nodes.len() >= 2
                && nodes[0].comp.is_c3()
                && nodes[1].comp.is_c6()
            {
                return PathProofNode::new_leaf("Manual proof for C3-C6-C5.".into(), true);
            }



                if nodes.len() >= 3
                    && nodes[0].comp.is_c3()
                    && nodes[1].comp.is_c3()
                    && nodes[2].comp.is_c4()
                {
                    return PathProofNode::new_leaf("Manual proof for C3-C3-C4.".into(), true);
                }
                if nodes.len() >= 3 && nodes[0].comp.is_c3() && nodes[1].comp.is_c6() {
                    let relevant_edges = edges.iter().filter(|e| e.between_path_nodes(1.into(), 2.into()));
                    for e in relevant_edges {
                        let c6_endpoint = e.endpoint_at(1.into()).unwrap();
                        if outside.iter().any(|&o| npc.is_nice_pair(*o, c6_endpoint)) {
                            return PathProofNode::new_leaf(
                                "Manual proof for C3-C6: Better nice path found!".into(),
                                true,
                            );
                        }
                    }
                }

                for c5 in nodes.iter().filter(|c| c.comp.is_c5()) {
                    if !c5.path_idx.is_last() && edges.iter().all(|e| !e.path_incident(c5.path_idx) || (e.path_incident(c5.path_idx.succ().unwrap()) || e.path_incident(c5.path_idx.prec()))) {
                        if outside.iter().filter(|n| c5.comp.contains(n)).count() >= 1 {
                            return PathProofNode::new_leaf(
                                "Manual proof for in=out-C5: Better nice path found!".into(),
                                true,
                            );
                        }
                    }
                }

                if nodes.len() >= 3 && nodes[0].comp.is_c3() && nodes[1].comp.is_c6() && nodes[2].comp.is_c5() {
                    if rem_edges.iter().filter(|e| e.source_idx.is_last()).count() >= 2 {
                            return PathProofNode::new_leaf(
                                "Manual proof for C3-C6-C5 with double C3-REM!".into(),
                                true,
                            );
                    }
                }

                              
                PathProofNode::new_leaf("No manual proof!".into(), false)
            }
            Tactic::TacticsExhausted => PathProofNode::new_leaf("Tactics exhausted!".into(), false),
            Tactic::Print => {
                let all_edges = stack.all_edges();
                let outside = stack.out_edges().collect_vec();
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

fn inductive_proof(sc: bool) -> Expression {
    induction_step(induction_step(or3( expr(Tactic::ManualCheck), expr(Tactic::Print), expr(Tactic::TacticsExhausted)), sc), sc)
}

fn induction_step(step: Expression, sc: bool) -> Expression {
    all(
        Enumerator::PathNodes,
        all_sc(
            Enumerator::NicePairs,
            or4(
                expr(Tactic::Print),
                expr(Tactic::ManualCheck),
                progress(),
                find_all_edges(step),
            ),
        ),
        sc,
    )
}

fn find_all_edges(otherwise: Expression) -> Expression {
    find_edge(
        find_edge(
            find_edge(
                find_edge(
                    find_edge(
                        find_edge(
                            find_edge(
                                find_edge(
                                    find_edge(otherwise.clone(), otherwise.clone()),
                                    otherwise.clone(),
                                ),
                                otherwise.clone(),
                            ),
                            otherwise.clone(),
                        ),
                        otherwise.clone(),
                    ),
                    otherwise.clone(),
                ),
                otherwise.clone(),
            ),
            otherwise.clone(),
        ),
        otherwise,
    )
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

pub fn prove_nice_path_progress(
    comps: Vec<Component>,
    last_comps: Vec<Component>,
    credit_inv: &CreditInv,
    output_dir: PathBuf,
    output_depth: usize,
    sc: bool,
    parallel: bool,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    let nodes = comps
        .into_iter()
        .flat_map(|comp| {
            if comp.is_c5() {
                vec![PathNode::Unused(comp.clone()), PathNode::Used(comp.clone())]
            } else {
                vec![PathNode::Unused(comp.clone())]
            }
        })
        .collect_vec();

    let last_nodes = last_comps
        .into_iter()
        .flat_map(|comp| {
            if comp.is_c5() {
                vec![PathNode::Unused(comp.clone()), PathNode::Used(comp.clone())]
            } else {
                vec![PathNode::Unused(comp.clone())]
            }
        })
        .collect_vec();

    let proof_cases = last_nodes;

    if parallel {
        proof_cases.into_par_iter().for_each(|last_node| {
            prove_last_node(
                nodes.clone(),
                last_node,
                credit_inv.clone(),
                &output_dir,
                output_depth,
                sc,
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
                sc,
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
    sc: bool,
) {
    // let mut context = PathContext {
    //     credit_inv: credit_inv.clone(),
    // };

    // let mut proof_tactic = inductive_proof(nodes.clone(), sc);

    // let mut proof = proof_tactic.action(
    //     &PathEnumeratorInput::new(last_node.clone(), nodes),
    //     &mut context,
    // );
    //proof_tactic.print_stats();
    let comp = last_node.get_comp().clone();

    let path_comp = PathComp {
        in_node: Some(comp.fixed_node().unwrap()),
        out_node: None,
        comp,
        used: last_node.is_used(),
        path_idx: Pidx::Last,
    };

    let mut instance = Instance {
        stack: vec![StackElement::Inst(InstPart::new_path_comp(path_comp))],
        context: InstanceContext {
            inv: credit_inv.clone(),
            comps: nodes,
        },
        matching_edge_id_counter: MatchingEdgeId(0),
    };

    let expr = inductive_proof(sc);
    let mut proof = expr.prove(&mut instance);
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
