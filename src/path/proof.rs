use std::fmt::Write;
use std::{marker::PhantomData, path::PathBuf};

use itertools::Itertools;
use rayon::prelude::{IntoParallelRefIterator, ParallelBridge, ParallelIterator, IntoParallelIterator};

use crate::path::enumerators::expand::{ExpandEnum, ExpandLastEnum};
use crate::path::enumerators::expand_all::ExpandAllEnum;
use crate::path::enumerators::matching_edges::FindMatchingEdgesEnum;
use crate::path::enumerators::pseudo_cycles::PseudoCyclesEnum;
use crate::path::tactics::cycle_rearrange::CycleRearrangeTactic;
use crate::path::tactics::double_cycle_merge::DoubleCycleMergeTactic;
use crate::path::tactics::pendant_rewire::PendantRewireTactic;
use crate::path::tactics::swap_pseudo_cycle::CycleMergeViaSwap;
use crate::path::SelectedHitInstance;
use crate::{
    comps::{Component, CreditInvariant, DefaultCredits},
    proof_tree::ProofNode,
};

use super::enumerators::comp_hits::ComponentHitEnum;
use super::enumerators::matching_hits::MatchingHitEnum;
use super::enumerators::matching_nodes::MatchingNodesEnum;
use super::enumerators::nice_paths::{PathEnum, PathEnumeratorInput};
use super::tactics::contract::ContractabilityTactic;
use super::tactics::cycle_merge::CycleMergeTactic;
use super::tactics::local_merge::LocalMergeTactic;
use super::tactics::longer_path::LongerPathTactic;
use super::AugmentedPathInstance;

#[derive(Clone)]
pub struct ProofContext {
    pub credit_inv: DefaultCredits,
    pub path_len: usize,
}

pub trait EnumeratorTactic<I, O> {
    type Enumer<'a>: Enumerator<O>
    where
        Self: 'a,
        I: 'a;

    fn msg(&self, data_in: &I) -> String;
    fn get_enumerator<'a>(&'a self, data: &'a I) -> Self::Enumer<'a>;
    fn item_msg(&self, item: &O) -> String;
    fn precondition(&self, data: &I, context: &ProofContext) -> bool {
        true
    }
}

pub trait Enumerator<O> {
    fn iter(&self, context: &ProofContext) -> Box<dyn Iterator<Item = O> + '_>;
}

pub trait Tactic<I> {
    fn precondition(&self, data: &I, context: &ProofContext) -> bool;

    fn action(&mut self, data: &I, context: &ProofContext) -> ProofNode;
}

pub trait Statistics {
    fn print_stats(&self);
}

#[derive(Clone)]
pub struct If<I, A, F>
where
    F: Fn(&I) -> bool,
{
    tactic: A,
    cond: F,
    _phantom_data: PhantomData<I>,
}

impl<I, A, F> Statistics for If<I, A, F>
where
    A: Statistics,
    F: Fn(&I) -> bool,
{
    fn print_stats(&self) {
        self.tactic.print_stats()
    }
}

impl<I, A, F> Tactic<I> for If<I, A, F>
where
    A: Statistics + Tactic<I>,
    F: Fn(&I) -> bool,
{
    fn precondition(&self, data: &I, _context: &ProofContext) -> bool {
        (self.cond)(data)
    }

    fn action(&mut self, data: &I, context: &ProofContext) -> ProofNode {
        self.tactic.action(data, context)
    }
}

pub fn ifcond<I, A, F>(cond: F, tactic: A) -> If<I, A, F>
where
    F: Fn(&I) -> bool,
{
    If {
        tactic,
        cond,
        _phantom_data: PhantomData,
    }
}

#[derive(Clone)]
pub struct Or<I, A1, A2>
{
    tactic1: A1,
    tactic2: A2,
    _phantom_data: PhantomData<I>,
}

impl<I, A1, A2> Statistics for Or<I, A1, A2>
where
    A1: Statistics,
    A2: Statistics,
{
    fn print_stats(&self) {
        self.tactic1.print_stats();
        self.tactic2.print_stats();
    }
}

pub fn or<I, A1, A2>(tactic1: A1, tactic2: A2) -> Or<I, A1, A2>
{
    Or {
        tactic1,
        tactic2,
        _phantom_data: PhantomData,
    }
}

pub fn or3<I, A1, A2, A3>(tactic1: A1, tactic2: A2, tactic3: A3) -> Or<I, A1, Or<I, A2, A3>>
{
    or(tactic1, or(tactic2, tactic3))
}

pub fn or4<I, A1, A2, A3, A4>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
) -> Or<I, A1, Or<I, A2, Or<I, A3, A4>>>
{
    or3(tactic1, tactic2, or(tactic3, tactic4))
}

pub fn or5<I, A1, A2, A3, A4, A5>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, A5>>>>
{
    or4(tactic1, tactic2, tactic3, or(tactic4, tactic5))
}

pub fn or6<I, A1, A2, A3, A4, A5, A6>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
    tactic6: A6,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, Or<I, A5, A6>>>>>
{
    or5(tactic1, tactic2, tactic3, tactic4, or(tactic5, tactic6))
}

pub fn or7<I, A1, A2, A3, A4, A5, A6, A7>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
    tactic6: A6,
    tactic7: A7,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, Or<I, A5, Or<I, A6, A7>>>>>>
{
    or6(
        tactic1,
        tactic2,
        tactic3,
        tactic4,
        tactic5,
        or(tactic6, tactic7),
    )
}

impl<I, A1, A2> Tactic<I> for Or<I, A1, A2>
where
    A1: Tactic<I>,
    A2: Tactic<I>,
{
    fn action(&mut self, data: &I, context: &ProofContext) -> ProofNode {
        if self.tactic1.precondition(data, context) {
            let mut proof1 = self.tactic1.action(data, context);
            let outcome = proof1.eval();
            if outcome.success() || !self.tactic2.precondition(data, context) {
                return proof1;
            } else {
                let proof2 = self.tactic2.action(data, context);
                return ProofNode::new_or(proof1, proof2);
            }
        } else {
            self.tactic2.action(data, context)
        }
    }

    fn precondition(&self, data: &I, context: &ProofContext) -> bool {
        self.tactic1.precondition(data, context) || self.tactic2.precondition(data, context)
    }
}

#[derive(Clone)]
pub struct All<O, E, A>
{
    enum_tactic: E,
    item_tactic: A,
    short_circuiting: bool,
    parallel: bool,
    _phantom_data: PhantomData<O>,
}

pub fn all<O, E, A>(enum_tactic: E, item_tactic: A) -> All<O, E, A>

{
    All {
        enum_tactic,
        item_tactic,
        parallel: false,
        short_circuiting: true,
        _phantom_data: PhantomData,
    }
}

pub fn all_sc<O, E, A>(sc: bool, enum_tactic: E, item_tactic: A) -> All<O, E, A>
{
    All {
        enum_tactic,
        item_tactic,
        short_circuiting: sc,
        parallel: false,
        _phantom_data: PhantomData,
    }
}


impl<O, E, A> Statistics for All<O, E, A>
where
    A: Statistics,
{
    fn print_stats(&self) {
        self.item_tactic.print_stats();
    }
}

impl<E, A, I, O> Tactic<I> for All<O, E, A>
where
    E: EnumeratorTactic<I, O>,
    A: Tactic<O>
{
    fn action(&mut self, data_in: &I, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_all(self.enum_tactic.msg(&data_in));

        let enumerator = self.enum_tactic.get_enumerator(data_in);

        // if self.parallel {
        //     let proof_nodes: Vec<ProofNode> = enumerator
        //         .iter(context)
        //         .collect_vec()
        //         .into_iter()
        //         .par_bridge()
        //         .map(|d| {
        //             if !self.item_tactic.precondition(&d, context) {
        //                 ProofNode::new_leaf("wrong precondition".into(), false)
        //             } else {
        //                 let item_msg = self.enum_tactic.item_msg(&d);
        //                 let mut proof_item = self.item_tactic.clone().action(&d, context);
        //                 proof_item = ProofNode::new_info(item_msg, proof_item);
        //                 let outcome = proof_item.eval();
        //                 proof_item
        //             }
        //         })
        //         .collect();

        //     for proof_node in proof_nodes {
        //         proof.add_child(proof_node);
        //     }

        //     proof.eval();
        // } else {
            for d in enumerator.iter(context) {
                let res = if !self.item_tactic.precondition(&d, context) {
                    false
                } else {
                    let item_msg = self.enum_tactic.item_msg(&d);
                    let mut proof_item = self.item_tactic.action(&d, context);
                    proof_item = ProofNode::new_info(item_msg, proof_item);
                    let outcome = proof_item.eval();
                    proof.add_child(proof_item);
                    outcome.success()
                };

                if !res && self.short_circuiting {
                    break;
                }
            }
        //}

        proof
    }

    fn precondition(&self, data: &I, context: &ProofContext) -> bool {
        self.enum_tactic.precondition(data, context)
    }
}

#[derive(Clone)]
pub struct Any<O, E, A> {
    enum_tactic: E,
    item_tactic: A,
    _phantom_data: PhantomData<O>,
}

pub fn any<O, E, A>(enumerator: E, tactic: A) -> Any<O, E, A> {
    Any {
        enum_tactic: enumerator,
        item_tactic: tactic,
        _phantom_data: PhantomData,
    }
}

impl<O, E, A> Statistics for Any<O, E, A>
where
    A: Statistics,
{
    fn print_stats(&self) {
        self.item_tactic.print_stats();
    }
}

impl<E, A, I, O> Tactic<I> for Any<O, E, A>
where
    E: EnumeratorTactic<I, O>,
    A: Tactic<O>,
{
    fn action(&mut self, data_in: &I, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_any(self.enum_tactic.msg(&data_in));

        let enumerator = self.enum_tactic.get_enumerator(data_in);
        enumerator.iter(context).any(|d| {
            if !self.item_tactic.precondition(&d, context) {
                false
            } else {
                let item_msg = self.enum_tactic.item_msg(&d);
                let mut proof_item = self.item_tactic.action(&d, context);
                proof_item = ProofNode::new_info(item_msg, proof_item);
                let outcome = proof_item.eval();
                proof.add_child(proof_item);
                outcome.success()
            }
        });

        proof
    }

    fn precondition(&self, data: &I, context: &ProofContext) -> bool {
        self.enum_tactic.precondition(data, context)
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

    fn short_name(&self) -> String {
        match self {
            PathNode::Used(c) => format!("aided-{}", c.short_name()),
            PathNode::Unused(c) => c.short_name(),
        }
    }
}

pub fn prove_nice_path_progress<C: CreditInvariant + Send + Sync>(
    comps: Vec<Component>,
    last_comps: Vec<Component>,
    credit_inv: C,
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
        last_nodes.into_par_iter().for_each(|last_node| prove_last_node(nodes.clone(), last_node, credit_inv.clone(), &output_dir, output_depth, sc))
    } else {
        last_nodes.into_iter().for_each(|last_node| prove_last_node(nodes.clone(), last_node, credit_inv.clone(), &output_dir, output_depth, sc))
    };
}


fn prove_last_node<C: CreditInvariant>(nodes: Vec<PathNode>,
    last_node: PathNode,
    credit_inv: C,
    output_dir: &PathBuf,
    output_depth: usize,
    sc: bool,
    ) {
    let path_length = 4;
    let c = credit_inv.complex_black(2);


    let mut context = ProofContext {
        credit_inv: DefaultCredits::new(c),
        path_len: path_length,
    };

    let mut proof_tactic = all_sc(
        sc,
        PathEnum,
        get_path_tactic(sc, path_length)
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

fn get_path_tactic(sc: bool, path_len: usize) -> impl Tactic<AugmentedPathInstance> + Statistics  {
    all_sc(
        sc,
        MatchingHitEnum::for_comp(path_len - 1),
        all_sc(
            sc,
            ExpandLastEnum,
            or6(
                CountTactic::new("AugmentedPathInstances".into()),
                LongerPathTactic::new(),
                ContractabilityTactic::new(),
                any(
                    PseudoCyclesEnum,
                    or(CycleMergeTactic::new(), CycleRearrangeTactic::new()),
                ),
                any(
                    ComponentHitEnum,
                    all(
                        MatchingNodesEnum,
                        all(
                            ExpandEnum,
                            or6(
                                PendantRewireTactic::new(),
                                LocalMergeTactic::new(true),
                                any(PseudoCyclesEnum, CycleMergeTactic::new()),
                                LongerPathTactic::new(),
                                CycleMergeViaSwap::new(),
                                ifcond(
                                    |instance: &SelectedHitInstance| instance.last_hit,
                                all(
                                    ExpandAllEnum,
                                    or3(
                                        CountTactic::new(
                                            "Fully expanded AugmentedPathInstances".into(),
                                        ),
                                        any(PseudoCyclesEnum, CycleMergeTactic::new()),
                                        all(
                                            FindMatchingEdgesEnum,
                                            all(
                                                ExpandAllEnum,
                                                or5(
                                                    DoubleCycleMergeTactic::new(),
                                                    LocalMergeTactic::new(false),
                                                    LongerPathTactic::new(),
                                                    any(PseudoCyclesEnum, CycleMergeTactic::new()),
                                                    all(
                                                        FindMatchingEdgesEnum,
                                                        all(
                                                            ExpandAllEnum,
                                                            or5(
                                                                DoubleCycleMergeTactic::new(
                                                                ),
                                                                LocalMergeTactic::new(false),
                                                                LongerPathTactic::new(),
                                                                any(PseudoCyclesEnum, CycleMergeTactic::new()),
                                                                all(
                                                                    FindMatchingEdgesEnum,
                                                                    all(
                                                                        ExpandAllEnum,
                                                                        or4(
                                                                            DoubleCycleMergeTactic::new(
                                                                            ),
                                                                            LocalMergeTactic::new(false),
                                                                            LongerPathTactic::new(),
                                                                            any(PseudoCyclesEnum, CycleMergeTactic::new()),
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
                TacticsExhausted::new(),
            ),
        )
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

impl Tactic<AugmentedPathInstance> for TacticsExhausted {
    fn precondition(&self, _data: &AugmentedPathInstance, _context: &ProofContext) -> bool {
        true
    }

    fn action(&mut self, _data: &AugmentedPathInstance, _context: &ProofContext) -> ProofNode {
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

impl Tactic<AugmentedPathInstance> for CountTactic {
    fn precondition(&self, _data: &AugmentedPathInstance, _context: &ProofContext) -> bool {
        true
    }

    fn action(&mut self, _data: &AugmentedPathInstance, _context: &ProofContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf("".into(), false)
    }
}

impl Statistics for CountTactic {
    fn print_stats(&self) {
        println!("{} {}", self.name, self.num_calls)
    }
}
