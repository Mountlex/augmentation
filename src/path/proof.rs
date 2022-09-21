use std::fmt::Write;
use std::{marker::PhantomData, path::PathBuf};

use itertools::Itertools;
use rayon::prelude::{IntoParallelRefIterator, ParallelIterator};

use crate::path::enumerators::cycles_edges::CycleEdgeEnumTactic;
use crate::path::enumerators::pseudo_cycles::PseudoCyclesEnumTactic;
use crate::path::tactics::cycle_rearrange::CycleRearrangeTactic;
use crate::path::tactics::double_cycle_merge::DoubleCycleMergeTactic;
use crate::path::tactics::pendant_rewire::PendantRewireTactic;
use crate::path::tactics::swap_pseudo_cycle::CycleMergeViaMatchingSwap;
use crate::{
    comps::{Component, CreditInvariant, DefaultCredits},
    proof_tree::ProofNode,
};

use super::enumerators::comp_hits::ComponentHitEnumTactic;
use super::enumerators::matching_hits::MatchingHitEnumTactic;
use super::enumerators::matching_nodes::MatchingNodesEnumTactic;
use super::enumerators::nice_pairs::NPCEnumTactic;
use super::enumerators::nice_paths::{PathEnumTactic, PathEnumeratorInput};
use super::tactics::complex_merge::LocalComplexMerge;
use super::tactics::contract::ContractabilityTactic;
use super::tactics::cycle_merge::CycleMerge;
use super::tactics::local_merge::LocalMerge;
use super::tactics::longer_path::LongerPathTactic;
use super::tactics::longer_path_swap::LongerNicePathViaMatchingSwap;
use super::PathMatchingInstance;

pub struct ProofContext {
    pub credit_inv: DefaultCredits,
    pub path_len: usize,
}

pub trait EnumeratorTactic<I, O> {
    type Enumer<'a>: Enumerator<I, O>
    where
        Self: 'a,
        I: 'a;

    fn msg(&self, data_in: &I) -> String;
    fn get_enumerator<'a>(&'a self, data: &'a I) -> Self::Enumer<'a>;
    fn item_msg(&self, item: &O) -> String;
}

pub trait Enumerator<I, O> {
    fn iter(&mut self, context: &mut ProofContext) -> Box<dyn Iterator<Item = O> + '_>;
}

pub trait Tactic<I> {
    fn precondition(&self, data: &I, context: &ProofContext) -> bool;

    fn action(&mut self, data: &I, context: &mut ProofContext) -> ProofNode;
}

pub trait Statistics {
    fn print_stats(&self);
}

pub struct Or<I, A1, A2> {
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

pub fn or<I, A1, A2>(tactic1: A1, tactic2: A2) -> Or<I, A1, A2> {
    Or {
        tactic1,
        tactic2,
        _phantom_data: PhantomData,
    }
}

pub fn or3<I, A1, A2, A3>(tactic1: A1, tactic2: A2, tactic3: A3) -> Or<I, A1, Or<I, A2, A3>> {
    or(tactic1, or(tactic2, tactic3))
}

pub fn or4<I, A1, A2, A3, A4>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
) -> Or<I, A1, Or<I, A2, Or<I, A3, A4>>> {
    or3(tactic1, tactic2, or(tactic3, tactic4))
}

pub fn or5<I, A1, A2, A3, A4, A5>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, A5>>>> {
    or4(tactic1, tactic2, tactic3, or(tactic4, tactic5))
}

pub fn or6<I, A1, A2, A3, A4, A5, A6>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
    tactic6: A6,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, Or<I, A5, A6>>>>> {
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
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, Or<I, A5, Or<I, A6, A7>>>>>> {
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
    I: Clone,
{
    fn action(&mut self, data: &I, context: &mut ProofContext) -> ProofNode {
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

pub struct All<O, E, A> {
    enum_tactic: E,
    item_tactic: A,
    short_circuiting: bool,
    _phantom_data: PhantomData<O>,
}

pub fn all<O, E, A>(enum_tactic: E, item_tactic: A) -> All<O, E, A> {
    All {
        enum_tactic,
        item_tactic,
        short_circuiting: true,
        _phantom_data: PhantomData,
    }
}

pub fn all_sc<O, E, A>(sc: bool, enum_tactic: E, item_tactic: A) -> All<O, E, A> {
    All {
        enum_tactic,
        item_tactic,
        short_circuiting: sc,
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
    A: Tactic<O>,
{
    fn action(&mut self, data_in: &I, context: &mut ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_all(self.enum_tactic.msg(&data_in));

        let mut enumerator = self.enum_tactic.get_enumerator(data_in);

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

        proof
    }

    fn precondition(&self, _data: &I, _contextt: &ProofContext) -> bool {
        true
    }
}

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
    fn action(&mut self, data_in: &I, context: &mut ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_any(self.enum_tactic.msg(&data_in));

        let mut enumerator = self.enum_tactic.get_enumerator(data_in);
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

    fn precondition(&self, _data: &I, _contextt: &ProofContext) -> bool {
        true
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

pub fn prove_nice_path_progress<C: CreditInvariant + Sync + Send>(
    comps: Vec<Component>,
    last_comps: Vec<Component>,
    credit_inv: C,
    output_dir: PathBuf,
    output_depth: usize,
    sc: bool,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    let c = credit_inv.complex_black(2);

    let path_length = 4;

    let nodes = comps
        .into_iter()
        .flat_map(|comp| {
            if comp.is_c5() {
                vec![PathNode::Used(comp.clone()), PathNode::Unused(comp.clone())]
            } else {
                vec![PathNode::Unused(comp.clone())]
            }
        })
        .collect_vec();

    let last_nodes = last_comps
        .into_iter()
        .flat_map(|comp| {
            if comp.is_c5() {
                vec![PathNode::Used(comp.clone()), PathNode::Unused(comp.clone())]
            } else {
                vec![PathNode::Unused(comp.clone())]
            }
        })
        .collect_vec();

    last_nodes.par_iter().for_each(|last_comp| {
        let mut context = ProofContext {
            credit_inv: DefaultCredits::new(c),
            path_len: path_length,
        };

        let mut proof_tactic = all_sc(
            sc,
            PathEnumTactic,
            all_sc(
                sc,
                MatchingHitEnumTactic::for_comp(path_length - 1),
                all_sc(
                    sc,
                    NPCEnumTactic,
                    or7(
                        CountTactic::new(),
                        LongerPathTactic::new(),
                        ContractabilityTactic::new(),
                        any(
                            CycleEdgeEnumTactic,
                            all(PseudoCyclesEnumTactic::new(true), CycleMerge::new()),
                        ),
                        any(
                            ComponentHitEnumTactic,
                            or(
                                LocalComplexMerge::new(),
                                all(
                                    MatchingNodesEnumTactic,
                                    all(
                                        NPCEnumTactic,
                                        or4(
                                            LocalMerge::new(),
                                            LongerNicePathViaMatchingSwap::new(),
                                            PendantRewireTactic::new(),
                                            CycleMergeViaMatchingSwap::new(),
                                        ),
                                    ),
                                ),
                            ),
                        ),
                        any(
                            CycleEdgeEnumTactic,
                            all(
                                PseudoCyclesEnumTactic::new(true),
                                or(DoubleCycleMergeTactic::new(), CycleRearrangeTactic::new()),
                            ),
                        ),
                        TacticsExhausted::new(),
                    ),
                ),
            ),
        );

        let mut proof = proof_tactic.action(
            &PathEnumeratorInput::new(last_comp.clone(), nodes.clone()),
            &mut context,
        );

        let outcome = proof.eval();

        println!(
            "Results for nice paths ending with {}",
            last_comp.short_name()
        );
        proof_tactic.print_stats();

        let filename = if outcome.success() {
            println!(
                "✔️ Proved nice path progress ending in {}",
                last_comp.short_name()
            );
            output_dir.join(format!("proof_{}.txt", last_comp.short_name()))
        } else {
            println!(
                "❌ Disproved nice path progress ending in {}",
                last_comp.short_name()
            );
            output_dir.join(format!("wrong_proof_{}.txt", last_comp.short_name()))
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
    });
}

struct TacticsExhausted {
    num_calls: usize,
}

impl TacticsExhausted {
    fn new() -> Self {
        Self { num_calls: 0 }
    }
}

impl Tactic<PathMatchingInstance> for TacticsExhausted {
    fn precondition(&self, _data: &PathMatchingInstance, _context: &ProofContext) -> bool {
        true
    }

    fn action(&mut self, _data: &PathMatchingInstance, _context: &mut ProofContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf("Tactics exhausted!".into(), false)
    }
}

impl Statistics for TacticsExhausted {
    fn print_stats(&self) {
        println!("Unproved path matching instances {}", self.num_calls)
    }
}

struct CountTactic {
    num_calls: usize,
}

impl CountTactic {
    fn new() -> Self {
        Self { num_calls: 0 }
    }
}

impl Tactic<PathMatchingInstance> for CountTactic {
    fn precondition(&self, _data: &PathMatchingInstance, _context: &ProofContext) -> bool {
        true
    }

    fn action(&mut self, _data: &PathMatchingInstance, _context: &mut ProofContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf("".into(), false)
    }
}

impl Statistics for CountTactic {
    fn print_stats(&self) {
        println!("PathMatchingInstances {}", self.num_calls)
    }
}
