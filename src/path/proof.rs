use chrono::prelude::*;
use std::fmt::Write;
use std::path::PathBuf;

use itertools::Itertools;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

use crate::path::instance::{InstanceContext, PathNode};
use crate::path::{PathComp, PathProofNode, Pidx};
use crate::{comps::Component, CreditInv};

use super::enumerators::{path_comp_enumerator, Enumerator, OptEnumerator};
use super::instance::{InstPart, Instance, StackElement};
use super::tactics::Tactic;
use crate::logic::*;

type ProofExpr = Expression<Enumerator, OptEnumerator, Tactic, Mapper>;

#[derive(Clone, Debug)]
enum Mapper {
    ToFiniteInstance,
}

impl MapperTrait for Mapper {
    type Inst = Instance;
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

fn prove_progress(finite: bool, options: PathProofOptions, depth: u8) -> ProofExpr {
    if depth > 0 {
        or(progress(finite), split_cases(finite, options, depth - 1))
    } else {
        expr(Tactic::TacticsExhausted(false))
    }
}

fn split_cases(finite: bool, options: PathProofOptions, depth: u8) -> ProofExpr {
    all_opt(
        OptEnumerator::Edges(finite),
        prove_progress(finite, options, depth),
        if finite {
            expr(Tactic::TacticsExhausted(true))
        } else {
            // and(
            //     // finite case
            //     all_opt_par(
            //         OptEnumerator::PathNode,
            //         map(
            //             Mapper::ToFiniteInstance,
            //             prove_progress(true, options, depth),
            //         ),
            //         expr(Tactic::TacticsExhausted(true)),
            //         options.sc,
            //     ),
                // infinite case
                all_opt_par(
                    OptEnumerator::PathNode,
                    prove_progress(false, options, depth),
                    expr(Tactic::TacticsExhausted(false)),
                    options.sc,
                )
            // )
        },
        options.sc,
    )
}

fn progress(finite: bool) -> ProofExpr {
    or5(
        expr(Tactic::FastLongerPath(finite)),
        expr(Tactic::LocalMerge),
        expr(Tactic::Pendant),
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
    pub max_depth: u8,
    pub initial_node_depth: u8,
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

    // Prepare proof cases
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
        comp.nodes().to_vec()
    };

    let mut cases = in_nodes
        .into_iter()
        .map(|in_node| {
            // last comp
            let path_comp = PathComp {
                in_node: Some(in_node),
                out_node: None,
                comp: comp.clone(),
                used: last_node.is_used(),
                path_idx: Pidx::Last,
                initial_nps: comp.edges(),
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
        options.initial_node_depth,
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
            let expr = prove_progress(false, options, options.max_depth);
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
