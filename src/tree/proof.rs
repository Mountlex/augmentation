use std::fmt::Write;
use std::path::PathBuf;

use crate::{
    comps::Component,
    proof_logic::*,
    proof_tree::ProofNode,
    tree::{
        enumerators::{
            cases::CompEnum, contractable_comps::ContractableCompsEnum,
            contractable_edges::ContractableEdgesEnum, matching_edge::MatchingEnum,
        },
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
            MatchingEnum::new(3),
            or4(
                DirectMerge::new("2-Comp Merge".into()),
                any(
                    ContractableCompsEnum,
                    all(
                        ContractableEdgesEnum,
                        DirectMerge::new("2-Comp Merge via Contractability".into()),
                    ),
                ),
                ifcond(
                    |_instance: &TreeCaseInstance| true,
                    all(
                        CompEnum,
                        all(
                            MatchingEnum::new(3),
                            or(
                                DirectMerge::new("3-Comp Merge".into()),
                                any(
                                    ContractableCompsEnum,
                                    all(
                                        ContractableEdgesEnum,
                                        DirectMerge::new("3-Comp Merge via Contractability".into()),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
                TacticsExhausted::new(),
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

#[derive(Clone)]
struct TacticsExhausted {
    num_calls: usize,
}

impl TacticsExhausted {
    fn new() -> Self {
        Self { num_calls: 0 }
    }
}

impl Tactic<TreeCaseInstance, TreeContext> for TacticsExhausted {
    fn precondition(&self, _data: &TreeCaseInstance, _context: &TreeContext) -> bool {
        true
    }

    fn action(&mut self, _data: &TreeCaseInstance, _context: &TreeContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf("Tactics exhausted!".into(), false)
    }
}

impl Statistics for TacticsExhausted {
    fn print_stats(&self) {
        println!("Unproved tree matching instances {}", self.num_calls)
    }
}

#[derive(Clone)]
struct CountTactic {
    name: String,
    num_calls: usize,
}

impl CountTactic {
    #[allow(dead_code)]
    fn new(name: String) -> Self {
        Self { name, num_calls: 0 }
    }
}

impl Tactic<TreeCaseInstance, TreeContext> for CountTactic {
    fn precondition(&self, _data: &TreeCaseInstance, _context: &TreeContext) -> bool {
        true
    }

    fn action(&mut self, _data: &TreeCaseInstance, _context: &TreeContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf(String::new(), false)
    }
}

impl Statistics for CountTactic {
    fn print_stats(&self) {
        println!("{} {}", self.name, self.num_calls)
    }
}
