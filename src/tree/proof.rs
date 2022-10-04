use std::fmt::Write;
use std::path::PathBuf;

use crate::{
    comps::Component,
    proof_logic::*,
    tree::{
        enumerators::{cases::CompEnum, matching_edge::MatchingEnum},
        tactics::direct_merge::DirectMerge,
        TreeCaseInstance, TreeContext,
    },
    CreditInv,
};

pub fn prove_tree_case(
    comps: Vec<Component>,
    leaf_comp: Component,
    credit_inv: &CreditInv,
    output_dir: PathBuf,
    output_depth: usize,
    sc: bool,
    parallel: bool,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    let mut context = TreeContext {
        credit_inv: credit_inv.clone(),
        inner_comps: comps,
    };

    let mut proof_tactic = all_sc(
        sc,
        CompEnum,
        all_sc(
            sc,
            MatchingEnum,
            or(
                DirectMerge::new(),
                all_sc(
                    sc,
                    MatchingEnum,
                    or(
                        DirectMerge::new(),
                        all_sc(sc, MatchingEnum, or(DirectMerge::new(), DirectMerge::new())),
                    ),
                ),
            ),
        ),
    );

    let mut proof = proof_tactic.action(
        &TreeCaseInstance {
            comps: vec![leaf_comp.clone()],
            edges: vec![],
        },
        &mut context,
    );

    let outcome = proof.eval();

    println!("Results for tree case with leaf {}", leaf_comp.short_name());
    proof_tactic.print_stats();

    let filename = if outcome.success() {
        println!("✔️ Proved tree case with leaf {}", leaf_comp.short_name());
        output_dir.join(format!("proof_{}.txt", leaf_comp.short_name()))
    } else {
        println!(
            "❌ Disproved tree case with leaf {}",
            leaf_comp.short_name()
        );
        output_dir.join(format!("wrong_proof_{}.txt", leaf_comp.short_name()))
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
