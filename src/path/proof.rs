use std::fmt::{Display, Write};
use std::path::PathBuf;

use itertools::Itertools;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

use crate::path::{PathComp, Pidx};
use crate::{comps::Component, proof_tree::ProofNode, CreditInv};

use super::enumerators::edges::edge_enumerator;
use super::enumerators::nice_pairs::nice_pairs_enumerator;
use super::enumerators::path_nodes::path_node_enumerator;
use super::enumerators::pseudo_cycles::enumerate_pseudo_cycles;
use super::enumerators::rearrangements::enumerate_rearrangements;
use super::tactics::contract::check_contractability;
use super::tactics::cycle_merge::check_cycle_merge;
use super::tactics::local_merge::check_local_merge;
use super::tactics::longer_path::check_longer_nice_path;
use super::tactics::pendant_rewire::check_pendant_node;
use super::{InstPart, InstanceContext, PathNode, PseudoCycle, Rearrangement};

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

#[derive(Clone, Debug)]
pub struct Instance {
    stack: Vec<StackElement>,
    pub context: InstanceContext,
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
}

#[derive(Debug, Clone)]
enum Quantor {
    All(Enumerator, Box<Expression>),
    AllOpt(OptEnumerator, Box<Expression>, Box<Expression>),
    Any(Enumerator, Box<Expression>),
}

impl Quantor {
    fn formula(&self) -> &Box<Expression> {
        match self {
            Quantor::All(_, t) => t,
            Quantor::AllOpt(_, t, _) => t,
            Quantor::Any(_, t) => t,
        }
    }

    fn prove(&self, stack: &mut Instance) -> ProofNode {
        let (cases, otherwise) = match self {
            Quantor::All(e, _) => (Some(e.get_iter(stack)), None),
            Quantor::Any(e, _) => (Some(e.get_iter(stack)), None),
            Quantor::AllOpt(e, _, otherwise) => (e.try_iter(stack), Some(otherwise)),
        };

        if let Some(cases) = cases {
            let mut proof = match self {
                Quantor::All(e, _) => ProofNode::new_all(e.msg().to_string()),
                Quantor::AllOpt(e, _, _) => ProofNode::new_all(e.msg().to_string()),
                Quantor::Any(e, _) => ProofNode::new_any(e.msg().to_string()),
            };

            for instance in cases {
                let item_msg = format!("{}", instance);
                stack.push(instance);
                let mut proof_item = self.formula().prove(stack);
                proof_item = ProofNode::new_info(item_msg, proof_item);
                let outcome = proof_item.eval();
                proof.add_child(proof_item);
                let res = outcome.success();
                stack.pop();

                let should_break = match self {
                    Quantor::AllOpt(_, _, _) => !res,
                    Quantor::All(_, _) => !res,
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

    fn get_iter(&self, stack: &Instance) -> Vec<StackElement> {
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

    fn try_iter(&self, stack: &Instance) -> Option<Vec<StackElement>> {
        let iter = match self {
            OptEnumerator::Edges => edge_enumerator(stack),
        };

        if let Some(iter) = iter {
            Some(iter.map(|part| StackElement::Inst(part)).collect_vec())
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
    FiniteInstance,
    TacticsExhausted,
}

impl Tactic {
    fn prove(&self, stack: &Instance) -> ProofNode {
        match self {
            Tactic::LongerPath => check_longer_nice_path(stack),
            Tactic::CycleMerge => check_cycle_merge(stack),
            Tactic::LocalMerge => check_local_merge(stack),
            Tactic::Rearrangable => check_longer_nice_path(stack),
            Tactic::Contractable => check_contractability(stack),
            Tactic::Pendant => check_pendant_node(stack),
            Tactic::FiniteInstance => todo!(),
            Tactic::TacticsExhausted => ProofNode::new_leaf("Tactics exhausted!".into(), false),
        }
    }
}

#[derive(Debug, Clone)]
enum Expression {
    Quantor(Quantor),
    Tactic(Tactic),
    Or(Box<Expression>, Box<Expression>),
}

impl Expression {
    fn prove(&self, stack: &mut Instance) -> ProofNode {
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
                    ProofNode::new_or(proof1, proof2)
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

fn expr(tactic: Tactic) -> Expression {
    Expression::Tactic(tactic)
}

fn all(enumerator: Enumerator, expr: Expression) -> Expression {
    Expression::Quantor(Quantor::All(enumerator, Box::new(expr)))
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

fn inductive_proof() -> Expression {
    induction_step(induction_step(induction_step(induction_step(expr(
        Tactic::TacticsExhausted,
    )))))
}

fn induction_step(step: Expression) -> Expression {
    all(
        Enumerator::PathNodes,
        all(Enumerator::NicePairs, or(progress(), find_all_edges(step))),
    )
}

fn find_all_edges(otherwise: Expression) -> Expression {
    find_edge(
        find_edge(
            find_edge(
                find_edge(otherwise.clone(), otherwise.clone()),
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
        all(Enumerator::NicePairs, or(progress(), enumerator)),
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
    };

    let expr = inductive_proof();

    let mut proof = expr.prove(&mut instance);

    let outcome = proof.eval();

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

// fn inductive_proof(
//     comps: Vec<PathNode>,
//     sc: bool,
// ) -> impl Tactic<PathEnumeratorInput, PathContext> + Statistics {
//     induction_start(induction_steps(comps), sc)
//     //induction_start(TacticsExhausted::new(), sc)
// }

// fn induction_start<T>(
//     induction_steps: T,
//     sc: bool,
// ) -> impl Tactic<PathEnumeratorInput, PathContext> + Statistics
// where
//     T: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
// {
//     all_sc(
//         sc,
//         PathEnum, // Done
//         all(
//             ExpandLastEnum::new(false), // Done
//             all(
//                 MatchingHitEnum, // Done
//                 all(
//                     ExpandLastEnum::new(false), // Done
//                     or3(
//                         LongerPathTactic::new(false),
//                         any(
//                             PseudoCyclesEnum, // Done
//                             or(
//                                 CycleMergeTactic::new(),                                 // Done
//                                 any(PathRearrangementEnum, CycleRearrangeTactic::new()), // Done
//                             ),
//                         ),
//                         all(
//                             MatchingHitEnum,
//                             all(
//                                 ExpandAllEnum, // this also fixes matching edges
//                                 or(progress(), find_all_matching_edges(induction_steps)),
//                             ),
//                         ),
//                     ),
//                 ),
//             ),
//         ),
//     )
// }

// fn induction_steps(
//     comps: Vec<PathNode>,
// ) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone {
//     single_induction_step(
//         single_induction_step(
//             single_induction_step(TacticsExhausted::new(), comps.clone()),
//             comps.clone(),
//         ),
//         comps.clone(),
//     )
// }

// fn single_induction_step<T>(
//     step: T,
//     comps: Vec<PathNode>,
// ) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone
// where
//     T: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
// {
//     all(
//         IterCompEnum::new(comps), // Done
//         //or(
//             //progress(), // progress without expansion
//             all(
//                 ExpandAllEnum,
//                 or(
//                     progress(), // progress with expansion
//                     find_all_matching_edges(step),
//                 ),
//             //),
//         ),
//     )
// }

// fn find_all_matching_edges<T>(
//     otherwise: T,
// ) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone
// where
//     T: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
// {
//     find_matching_edge(
//         find_matching_edge(
//         find_matching_edge(
//         find_matching_edge(
//             find_matching_edge(
//                 find_matching_edge(otherwise.clone(), otherwise.clone()),
//                 otherwise.clone(),
//             ),
//             otherwise.clone(),
//             ),
//             otherwise.clone(),
//             ),
//             otherwise.clone(),
//         ),
//         otherwise.clone(),
//     )
// }

// fn find_matching_edge<T1, T2>(
//     enumerator: T1,
//     otherwise: T2,
// ) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone
// where
//     T1: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
//     T2: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
// {
//     all_opt(
//         FindMatchingEdgesEnum::new(false),
//         otherwise,
//         all(ExpandAllEnum, or(progress(), enumerator)),
//     )
// }
