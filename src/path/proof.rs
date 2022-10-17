use std::fmt::Write;
use std::path::PathBuf;

use itertools::Itertools;
use rayon::prelude::{IntoParallelIterator, ParallelIterator};

use crate::path::enumerators::expand::{ExpandEnum, ExpandLastEnum};
use crate::path::enumerators::expand_all::ExpandAllEnum;
use crate::path::enumerators::iter_comp::IterCompEnum;
use crate::path::enumerators::matching_edges::FindMatchingEdgesEnum;
use crate::path::enumerators::pseudo_cycles::PseudoCyclesEnum;
use crate::path::tactics::cycle_rearrange::CycleRearrangeTactic;
use crate::path::tactics::pendant_rewire::PendantRewireTactic;
use crate::path::SelectedHitInstance;
use crate::proof_tree::ProofNode;
use crate::{proof_logic::*, CreditInv};

use super::enumerators::comp_hits::ComponentHitEnum;
use super::enumerators::cycle_rearrangements::PathRearrangementEnum;
use super::enumerators::matching_hits::MatchingHitEnum;
use super::enumerators::matching_nodes::MatchingNodesEnum;
use super::enumerators::nice_paths::{PathEnum, PathEnumeratorInput};
use super::tactics::contract::ContractabilityTactic;
use super::tactics::cycle_merge::CycleMergeTactic;
use super::tactics::local_merge::LocalMergeTactic;
use super::tactics::longer_path::LongerPathTactic;
use super::AugmentedPathInstance;
use crate::comps::Component;

#[derive(Clone)]
pub struct PathContext {
    pub credit_inv: CreditInv,
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

    fn short_name(&self) -> String {
        match self {
            PathNode::Used(c) => format!("aided-{}", c.short_name()),
            PathNode::Unused(c) => c.short_name(),
        }
    }
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

    if parallel {
        last_nodes.into_par_iter().for_each(|last_node| {
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
        last_nodes.into_iter().for_each(|last_node| {
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
    let mut context = PathContext {
        credit_inv: credit_inv.clone(),
    };

    let mut proof_tactic = all_sc(
        sc,
        PathEnum,
        and(
            get_path_tactic(sc, true),
            all_sc(
                sc,
                IterCompEnum::new(nodes.clone()),
                or(
                    get_path_tactic(sc, false),
                    and(
                        get_path_tactic(sc, true),
                        all_sc(
                            sc,
                            IterCompEnum::new(nodes.clone()),
                            get_path_tactic(sc, false),
                        ),
                    ),
                ),
            ),
        ),
    );

    let mut proof = proof_tactic.action(
        &PathEnumeratorInput::new(last_node.clone(), nodes),
        &mut context,
    );

    let outcome = proof.eval();

    println!(
        "Results for nice paths ending with {}",
        last_node.short_name()
    );
    proof_tactic.print_stats();

    let filename = if outcome.success() {
        println!(
            "✔️ Proved nice path progress ending in {}",
            last_node.short_name()
        );
        output_dir.join(format!("proof_{}.txt", last_node.short_name()))
    } else {
        println!(
            "❌ Disproved nice path progress ending in {}",
            last_node.short_name()
        );
        output_dir.join(format!("wrong_proof_{}.txt", last_node.short_name()))
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

fn get_path_tactic(
    sc: bool,
    path_finite: bool,
) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics {
    all_sc(
        sc,
        ExpandLastEnum::new(path_finite),
        all_sc(
            sc,
            MatchingHitEnum,
            all_sc(
                sc,
                ExpandLastEnum::new(path_finite),
                or3(
                    LongerPathTactic::new(path_finite),
                    any(
                        PseudoCyclesEnum,
                        or(
                            CycleMergeTactic::new(),
                            any(PathRearrangementEnum, CycleRearrangeTactic::new()),
                        ),
                    ),
                    all_sc(
                        sc,
                        MatchingHitEnum,
                        all_sc(
                            sc,
                            ExpandLastEnum::new(path_finite),
                            or6(
                                CountTactic::new("AugmentedPathInstances".into()),
                                LongerPathTactic::new(path_finite),
                                ContractabilityTactic::new(),
                                any(
                                    PseudoCyclesEnum,
                                    or(
                                        CycleMergeTactic::new(),
                                        any(PathRearrangementEnum, CycleRearrangeTactic::new()),
                                    ),
                                ),
                                any(
                                    ComponentHitEnum,
                                    all(
                                        MatchingNodesEnum,
                                        all(
                                            ExpandEnum::new(path_finite),
                                            or5(
                                                PendantRewireTactic::new(),
                                                LocalMergeTactic::new(true),
                                                LongerPathTactic::new(path_finite),
                                                any(PseudoCyclesEnum, CycleMergeTactic::new()),
                                                ifcond(
                                                    |instance: &SelectedHitInstance| {
                                                        instance.last_hit
                                                    },
                                                    tryhard_mode(path_finite),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                                TacticsExhausted::new(),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

fn tryhard_mode(path_finite: bool) -> impl Tactic<SelectedHitInstance, PathContext> + Statistics {
    all(
        ExpandAllEnum,
        or4(
            CountTactic::new("Fully expanded AugmentedPathInstances".into()),
            LongerPathTactic::new(path_finite),
            any(
                PseudoCyclesEnum,
                or(
                    CycleMergeTactic::new(),
                    any(
                        PathRearrangementEnum,
                        or(
                            CycleRearrangeTactic::new(),
                            LongerPathTactic::new(path_finite),
                        ),
                    ),
                ),
            ),
            all(
                FindMatchingEdgesEnum::new(path_finite),
                all(
                    ExpandAllEnum,
                    or4(
                        LocalMergeTactic::new(false),
                        LongerPathTactic::new(path_finite),
                        any(
                            PseudoCyclesEnum,
                            or(
                                CycleMergeTactic::new(),
                                any(
                                    PathRearrangementEnum,
                                    or(
                                        CycleRearrangeTactic::new(),
                                        LongerPathTactic::new(path_finite),
                                    ),
                                ),
                            ),
                        ),
                        all(
                            FindMatchingEdgesEnum::new(path_finite),
                            all(
                                ExpandAllEnum,
                                or4(
                                    LongerPathTactic::new(path_finite),
                                    LocalMergeTactic::new(false),
                                    any(
                                        PseudoCyclesEnum,
                                        or(
                                            CycleMergeTactic::new(),
                                            any(
                                                PathRearrangementEnum,
                                                or(
                                                    CycleRearrangeTactic::new(),
                                                    LongerPathTactic::new(path_finite),
                                                ),
                                            ),
                                        ),
                                    ),
                                    all(
                                        FindMatchingEdgesEnum::new(path_finite),
                                        all(
                                            ExpandAllEnum,
                                            or3(
                                                LongerPathTactic::new(path_finite),
                                                LocalMergeTactic::new(false),
                                                any(
                                                    PseudoCyclesEnum,
                                                    or(
                                                        CycleMergeTactic::new(),
                                                        any(
                                                            PathRearrangementEnum,
                                                            or(
                                                                CycleRearrangeTactic::new(),
                                                                LongerPathTactic::new(path_finite),
                                                            ),
                                                        ),
                                                    ),
                                                ),
                                            ),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
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

impl Tactic<AugmentedPathInstance, PathContext> for TacticsExhausted {
    fn precondition(&self, _data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        true
    }

    fn action(&mut self, _data: &AugmentedPathInstance, _context: &PathContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf("Tactics exhausted!".into(), false)
    }
}

impl Statistics for TacticsExhausted {
    fn print_stats(&self) {
        println!("Unproved path matching instances {}", self.num_calls)
    }
}

#[derive(Clone)]
struct CountTactic {
    name: String,
    num_calls: usize,
}

impl CountTactic {
    fn new(name: String) -> Self {
        Self { name, num_calls: 0 }
    }
}

impl Tactic<AugmentedPathInstance, PathContext> for CountTactic {
    fn precondition(&self, _data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        true
    }

    fn action(&mut self, _data: &AugmentedPathInstance, _context: &PathContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf(String::new(), false)
    }
}

impl Statistics for CountTactic {
    fn print_stats(&self) {
        println!("{} {}", self.name, self.num_calls)
    }
}
