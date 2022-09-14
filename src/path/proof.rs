use std::fmt::Write;
use std::{marker::PhantomData, path::PathBuf};

use rayon::prelude::{IntoParallelIterator, ParallelIterator, IntoParallelRefIterator};

use crate::{
    comps::{Component, CreditInvariant, DefaultCredits},
    proof_tree::ProofNode,
};

use super::PathMatchingInstance;
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

impl<I, A1, A2> Tactic<I> for Or<I, A1, A2>
where
    A1: Tactic<I>,
    A2: Tactic<I>,
    I: Clone,
{
    fn action(&mut self, data: &I, context: &mut ProofContext) -> ProofNode {
        if self.tactic1.precondition(data, context) {
            let mut res1 = self.tactic1.action(data, context);
            let result = res1.eval();
            if result || !self.tactic2.precondition(data, context) {
                return res1;
            } else {
                let res2 = self.tactic2.action(data, context);
                return ProofNode::new_or(res1, res2);
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


pub fn all_sc<O, E, A>(sc: bool, enum_tactic: E, item_tactic: A,) -> All<O, E, A> {
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
                let mut res = self.item_tactic.action(&d, context);
                res = ProofNode::new_info(item_msg, res);
                let cont = res.eval();
                proof.add_child(res);
                cont
            };

            if !res && self.short_circuiting {
                break;
            }
        }

        proof
    }

    fn precondition(&self, data: &I, context: &ProofContext) -> bool {
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
        let mut proof = ProofNode::new_all(self.enum_tactic.msg(&data_in));

        let mut enumerator = self.enum_tactic.get_enumerator(data_in);
        enumerator.iter(context).any(|d| {
            if !self.item_tactic.precondition(&d, context) {
                false
            } else {
                let item_msg = self.enum_tactic.item_msg(&d);
                let mut res = self.item_tactic.action(&d, context);
                res = ProofNode::new_info(item_msg, res);
                let cont = res.eval();
                proof.add_child(res);
                cont
            }
        });

        proof
    }

    fn precondition(&self, data: &I, context: &ProofContext) -> bool {
        true
    }
}

pub fn prove_nice_path_progress<C: CreditInvariant + Sync + Send>(
    comps: Vec<Component>,
    credit_inv: C,
    output_dir: PathBuf,
    output_depth: usize,
    sc: bool,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    let c = credit_inv.complex_black(2);

    let path_length = 4;

    comps.par_iter().for_each(|last_comp| {
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
                    or6(
                                CountTactic::new(),
                        LongerPathTactic::new(),
                        ContractabilityTactic::new(),
                        any(
                            ComponentHitEnumTactic,
                            or(
                                LocalComplexMerge::new(),
                                all(
                                    MatchingNodesEnumTactic,
                                    all(
                                        NPCEnumTactic,
                                        or(LocalMerge::new(), LongerNicePathViaMatchingSwap::new()),
                                    ),
                                ),
                            ),
                        ),
                        CycleMerge::new(),
                        TacticsExhausted::new()
                    ),
                ),
            ),
        );

        let mut proof = proof_tactic.action(
            &PathEnumeratorInput::new(last_comp.clone(), comps.clone()),
            &mut context,
        );

        let proved = proof.eval();

        println!("Results for nice paths ending with {}", last_comp);
        proof_tactic.print_stats();

        let filename = if proved {
            log::info!("✔️ Proved nice path progress ending in {}", last_comp);
            output_dir.join(format!("proof_{}.txt", last_comp.short_name()))
        } else {
            log::warn!("❌ Disproved nice path progress ending in {}", last_comp);
            output_dir.join(format!("wrong_proof_{}.txt", last_comp.short_name()))
        };

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
    num_calls: usize
}

impl TacticsExhausted {
    fn new() -> Self {
        Self {
            num_calls: 0
        }
    }
}

impl Tactic<PathMatchingInstance> for TacticsExhausted {
    fn precondition(&self, data: &PathMatchingInstance, context: &ProofContext) -> bool {
        true    
    }

    fn action(&mut self, data: &PathMatchingInstance, context: &mut ProofContext) -> ProofNode {
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
    num_calls: usize
}

impl CountTactic {
    fn new() -> Self {
        Self {
            num_calls: 0
        }
    }
}

impl Tactic<PathMatchingInstance> for CountTactic {
    fn precondition(&self, data: &PathMatchingInstance, context: &ProofContext) -> bool {
        true    
    }

    fn action(&mut self, data: &PathMatchingInstance, context: &mut ProofContext) -> ProofNode {
        self.num_calls += 1;
        ProofNode::new_leaf("".into(), false)
    }
}

impl Statistics for CountTactic {
    fn print_stats(&self) {
        println!("PathMatchingInstances {}", self.num_calls)
    }
}
