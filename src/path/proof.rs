use std::fmt::Write;
use std::path::{self, PathBuf};

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
use crate::util::relabels_nodes_sequentially;
use crate::{proof_logic::*, Credit, CreditInv};

use super::enumerators::comp_hits::ComponentHitEnum;
use super::enumerators::cycle_rearrangements::PathRearrangementEnum;
use super::enumerators::matching_hits::MatchingHitEnum;
use super::enumerators::matching_nodes::MatchingNodesEnum;
use super::enumerators::nice_paths::{PathEnum, PathEnumeratorInput};
use super::tactics::contract::ContractabilityTactic;
use super::tactics::cycle_merge::CycleMergeTactic;
use super::tactics::local_merge::LocalMergeTactic;
use super::tactics::longer_path::LongerPathTactic;
use super::{AbstractNode, AugmentedPathInstance, Pidx, SuperNode};
use crate::comps::{c3, c4, c5, c6, large, CompType, Component};

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

    let k = ((Credit::from_integer(4) - Credit::from_integer(13) * credit_inv.c)
        / (Credit::from_integer(5) * credit_inv.c - Credit::from_integer(1)))
    .ceil()
    .to_integer() as usize;

    println!("k = {}", k);

    let last_nodes_with_depth = last_nodes
        .into_iter()
        .map(|c| {
            if c.get_comp().is_c4() || c.get_comp().is_c5() {
                (c.clone(), k + 3)
            } else {
                (c.clone(), 4)
            }
        })
        .collect_vec();

    let proof_cases = last_nodes_with_depth
        .into_iter()
        .flat_map(|(node, depth)| {
            std::iter::once((node.clone(), depth, false))
                .chain((3..depth).into_iter().map(move |d| (node.clone(), d, true)))
        })
        .collect_vec();

    if parallel {
        proof_cases
            .into_par_iter()
            .for_each(|(last_node, length, finite)| {
                prove_last_node(
                    nodes.clone(),
                    last_node,
                    length,
                    finite,
                    credit_inv.clone(),
                    &output_dir,
                    output_depth,
                    sc,
                )
            })
    } else {
        proof_cases
            .into_iter()
            .for_each(|(last_node, length, finite)| {
                prove_last_node(
                    nodes.clone(),
                    last_node,
                    length,
                    finite,
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
    length: usize,
    finite: bool,
    credit_inv: CreditInv,
    output_dir: &PathBuf,
    output_depth: usize,
    sc: bool,
) {
    let mut context = PathContext {
        credit_inv: credit_inv.clone(),
    };

    let mut proof = if length == 3 {
        let mut proof_tactic = all_sc(sc, PathEnum, get_path_tactic(sc, finite));

        let proof = proof_tactic.action(
            &PathEnumeratorInput::new(last_node.clone(), nodes),
            &mut context,
        );
        proof_tactic.print_stats();

        proof
    } else if length == 4 {
        let mut proof_tactic = all_sc(
            sc,
            PathEnum,
            all_sc(
                sc,
                IterCompEnum::new(nodes.clone()),
                get_path_tactic(sc, finite),
            ),
        );

        let proof = proof_tactic.action(
            &PathEnumeratorInput::new(last_node.clone(), nodes),
            &mut context,
        );
        proof_tactic.print_stats();

        proof
    } else if length == 5 {
        let mut proof_tactic = all_sc(
            sc,
            PathEnum,
            all_sc(
                sc,
                IterCompEnum::new(nodes.clone()),
                all_sc(
                    sc,
                    IterCompEnum::new(nodes.clone()),
                    get_path_tactic(sc, finite),
                ),
            ),
        );

        let proof = proof_tactic.action(
            &PathEnumeratorInput::new(last_node.clone(), nodes),
            &mut context,
        );
        proof_tactic.print_stats();

        proof
    } else {
        assert!(length == 6);
        let mut proof_tactic = all_sc(
            sc,
            PathEnum,
            all_sc(
                sc,
                IterCompEnum::new(nodes.clone()),
                all_sc(
                    sc,
                    IterCompEnum::new(nodes.clone()),
                    all_sc(
                        sc,
                        IterCompEnum::new(nodes.clone()),
                        get_path_tactic(sc, false),
                    ),
                ),
            ),
        );

        let proof = proof_tactic.action(
            &PathEnumeratorInput::new(last_node.clone(), nodes),
            &mut context,
        );
        proof_tactic.print_stats();

        proof
    };

    let outcome = proof.eval();

    let filename = if outcome.success() {
        println!(
            "✔️ Proved nice path progress ending in {} of length {}, finite={}",
            last_node.short_name(),
            length,
            finite
        );
        output_dir.join(format!(
            "proof_{}_{}_{}.txt",
            last_node.short_name(),
            length,
            finite
        ))
    } else {
        println!(
            "❌ Disproved nice path progress ending in {} of length {}, finite={}",
            last_node.short_name(),
            length,
            finite
        );
        output_dir.join(format!(
            "wrong_proof_{}_{}_{}.txt",
            last_node.short_name(),
            length,
            finite
        ))
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

pub fn test_instance() {
    let context = PathContext {
        credit_inv: CreditInv::new(Credit::new(1, 4)),
    };

    let path = vec![
        PathNode::Unused(c4()),
        PathNode::Unused(large()),
        PathNode::Unused(c4()),
        //PathNode::Unused(c5()),
        PathNode::Unused(c5()),
    ];
    let mut path_updated = path.iter().map(|n| n.get_comp().clone()).collect_vec();
    relabels_nodes_sequentially(&mut path_updated, 0);

    let path = path
        .into_iter()
        .zip(path_updated.into_iter())
        .map(|(o, n)| match o {
            PathNode::Used(_) => PathNode::Used(n),
            PathNode::Unused(_) => PathNode::Unused(n),
        })
        .collect_vec();

    let nodes = path
        .into_iter()
        .enumerate()
        .map(|(i, c)| -> SuperNode {
            let nice_pair = match c.get_comp().comp_type() {
                CompType::Cycle(num) if num <= 4 => true,
                CompType::Cycle(num) if num == 5 && i == 1 && !c.is_used() => true,
                CompType::Complex => true,
                _ => false,
            };

            let in_not_out = if c.get_comp().is_c5() && i == 1 {
                true
            } else {
                nice_pair
            };

            SuperNode::Abstract(AbstractNode {
                comp: c.get_comp().clone(),
                nice_pair,
                used: c.is_used(),
                in_not_out,
                path_idx: Pidx::from(i),
            })
        })
        .collect();

    let instance = AugmentedPathInstance {
        nodes,
        abstract_edges: vec![],
        fixed_edges: vec![],
    };

    let mut result = get_path_tactic(true, true).action(&instance, &context);
    result.eval();
    let mut buf = String::new();
    result
        .print_tree(&mut buf, 3)
        .expect("Unable to format tree");
    std::fs::write("test.txt", buf).expect("Unable to write file");
}



fn inductive_proof(comps: Vec<PathNode>) -> impl Tactic<PathEnumeratorInput, PathContext> + Statistics {
    induction_start(induction_steps(comps))
}


fn induction_start<T>(
    induction_steps: T,
) -> impl Tactic<PathEnumeratorInput, PathContext> + Statistics
where
    T: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
{
    all(
        PathEnum,
        all(
            ExpandLastEnum::new(false),
            all(
                MatchingHitEnum,
                all(
                    ExpandLastEnum::new(false),
                    or3(
                        LongerPathTactic::new(false),
                        any(
                            PseudoCyclesEnum,
                            or(
                                CycleMergeTactic::new(),
                                any(PathRearrangementEnum, CycleRearrangeTactic::new()),
                            ),
                        ),
                        all(
                            MatchingHitEnum,
                            all(
                                ExpandAllEnum,
                                or(progress(), find_all_matching_edges(induction_steps)),
                            ),
                        ),
                    ),
                ),
            ),
        ),
    )
}

fn induction_steps(
    comps: Vec<PathNode>,
) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone {
    single_induction_step(
        single_induction_step(
            single_induction_step(
                single_induction_step(
                    single_induction_step(
                        single_induction_step(
                            single_induction_step(
                                single_induction_step(TacticsExhausted::new(), comps.clone()),
                                comps.clone(),
                            ),
                            comps.clone(),
                        ),
                        comps.clone(),
                    ),
                    comps.clone(),
                ),
                comps.clone(),
            ),
            comps.clone(),
        ),
        comps.clone(),
    )
}

fn single_induction_step<T>(
    step: T,
    comps: Vec<PathNode>,
) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone
where
    T: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
{
    all(
        IterCompEnum::new(comps), // TODO fix RemPath
        all(
            MatchingHitEnum, // TODO rewrite
            or(
                progress(), // progress without expansion
                all(
                    ExpandAllEnum,
                    or(
                        progress(), // progress with expansion
                        find_all_matching_edges(step),
                    ),
                ),
            ),
        ),
    )
}

fn find_all_matching_edges<T>(
    otherwise: T,
) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone
where
    T: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
{
    find_matching_edge(
        find_matching_edge(
            find_matching_edge(
                find_matching_edge(
                    find_matching_edge(
                        find_matching_edge(otherwise.clone(), otherwise.clone()),
                        otherwise.clone(),
                    ),
                    otherwise.clone(),
                ),
                otherwise.clone(),
            ),
            otherwise.clone(),
        ),
        otherwise.clone(),
    )
}

fn find_matching_edge<T1, T2>(
    enumerator: T1,
    otherwise: T2,
) -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone
where
    T1: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
    T2: Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone,
{
    all_opt(
        FindMatchingEdgesEnum::new(false),
        otherwise,
        all(ExpandAllEnum, or(progress(), enumerator)),
    )
}

fn progress() -> impl Tactic<AugmentedPathInstance, PathContext> + Statistics + Clone {
    or3(
        LocalMergeTactic::new(),
        LongerPathTactic::new(false),
        any(
            PseudoCyclesEnum,
            or(
                CycleMergeTactic::new(),
                any(
                    PathRearrangementEnum,
                    or(CycleRearrangeTactic::new(), LongerPathTactic::new(false)),
                ),
            ),
        ),
    )
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
                                ContractabilityTactic::new(false),
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
                                                LocalMergeTactic::new(),
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
            all_opt(
                FindMatchingEdgesEnum::new(path_finite),
                FiniteInstance::new(path_finite),
                all(
                    ExpandAllEnum,
                    or4(
                        LocalMergeTactic::new(),
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
                        all_opt(
                            FindMatchingEdgesEnum::new(path_finite),
                            FiniteInstance::new(path_finite),
                            all(
                                ExpandAllEnum,
                                or4(
                                    LongerPathTactic::new(path_finite),
                                    LocalMergeTactic::new(),
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
                                    all_opt(
                                        FindMatchingEdgesEnum::new(path_finite),
                                        FiniteInstance::new(path_finite),
                                        all(
                                            ExpandAllEnum,
                                            or4(
                                                LongerPathTactic::new(path_finite),
                                                LocalMergeTactic::new(),
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
                                                all_opt(
                                                    FindMatchingEdgesEnum::new(path_finite),
                                                    FiniteInstance::new(path_finite),
                                                    all(
                                                        ExpandAllEnum,
                                                        or4(
                                                            LongerPathTactic::new(path_finite),
                                                            LocalMergeTactic::new(),
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
                                                            all_opt(
                                                                FindMatchingEdgesEnum::new(path_finite),
                                                                FiniteInstance::new(path_finite),
                                                                all(
                                                                    ExpandAllEnum,
                                                                    or4(
                                                                        LongerPathTactic::new(path_finite),
                                                                        LocalMergeTactic::new(),
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
                                                                        all_opt(
                                                                            FindMatchingEdgesEnum::new(path_finite),
                                                                            FiniteInstance::new(path_finite),
                                                                            all(
                                                                                ExpandAllEnum,
                                                                                or4(
                                                                                    LongerPathTactic::new(path_finite),
                                                                                    LocalMergeTactic::new(),
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
                                                                                    all_opt(
                                                                                        FindMatchingEdgesEnum::new(path_finite),
                                                                                        FiniteInstance::new(path_finite),
                                                                                        all(
                                                                                            ExpandAllEnum,
                                                                                            or4(
                                                                                                LongerPathTactic::new(path_finite),
                                                                                                LocalMergeTactic::new(),
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
                                                                                                all_opt(
                                                                                                    FindMatchingEdgesEnum::new(path_finite),
                                                                                                    FiniteInstance::new(path_finite),
                                                                                                    all(
                                                                                                        ExpandAllEnum,
                                                                                                        or4(
                                                                                                            LongerPathTactic::new(path_finite),
                                                                                                            LocalMergeTactic::new(),
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
                                                                                                            all_opt(
                                                                                                                FindMatchingEdgesEnum::new(path_finite),
                                                                                                                FiniteInstance::new(path_finite),
                                                                                                                all(
                                                                                                                    ExpandAllEnum,
                                                                                                                    or3(
                                                                                                                        LongerPathTactic::new(path_finite),
                                                                                                                        LocalMergeTactic::new(),
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
struct False;

impl Tactic<AugmentedPathInstance, PathContext> for False {
    fn precondition(&self, _data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        true
    }

    fn action(&mut self, _data: &AugmentedPathInstance, _context: &PathContext) -> ProofNode {
        ProofNode::new_leaf("False!".into(), false)
    }
}

impl Statistics for False {
    fn print_stats(&self) {
        println!("")
    }
}

#[derive(Clone)]
struct FiniteInstance {
    num_calls: usize,
    finite_instance: bool,
}

impl FiniteInstance {
    fn new(finite_instance: bool) -> Self {
        Self {
            num_calls: 0,
            finite_instance,
        }
    }
}

impl Tactic<AugmentedPathInstance, PathContext> for FiniteInstance {
    fn precondition(&self, _data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        self.finite_instance
    }

    fn action(&mut self, data: &AugmentedPathInstance, _context: &PathContext) -> ProofNode {
        self.num_calls += 1;
        if data.all_outside_hits().len() < 3 && data.nodes.iter().all(|n| n.get_comp().is_cycle()) {
            ProofNode::new_leaf(
                "Finite Instance but less than three outgoing edges!".into(),
                true,
            )
        } else {
            ProofNode::new_leaf("No Finite Instance!".into(), false)
        }
    }
}

impl Statistics for FiniteInstance {
    fn print_stats(&self) {
        println!("{}", self.num_calls)
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
