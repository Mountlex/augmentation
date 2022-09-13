use std::fmt::Write;
use std::{marker::PhantomData, path::PathBuf};

use crate::{
    comps::{Component, CreditInvariant, DefaultCredits},
    proof_tree::ProofNode,
};

use super::enumerators::comp_hits::ComponentHitEnumerator;
use super::enumerators::matching_hits::MatchingHitEnumerator;
use super::enumerators::matching_nodes::{MatchingNodesEnumerator};
use super::enumerators::nice_pairs::NPCEnumerator;
use super::enumerators::nice_paths::{PathEnumerator, PathEnumeratorInput};
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

pub trait Enumerator<I, O> {
    //type Iter: Iterator<Item = Self::Out>;

    fn msg(&self, data_in: &I) -> String;

    fn iter(&self, data_in: I, context: &ProofContext) -> Box<dyn Iterator<Item = O>>;

    fn item_msg(&self, item: &O) -> String;
}

pub trait Tactic<I> {
    fn action(&self, data: I, context: &ProofContext) -> ProofNode;
}

pub struct Or<I, A1, A2> {
    tactic1: A1,
    tactic2: A2,
    _phantom_data: PhantomData<I>,
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

impl<I, A1, A2> Tactic<I> for Or<I, A1, A2>
where
    A1: Tactic<I>,
    A2: Tactic<I>,
    I: Clone,
{
    fn action(&self, data: I, context: &ProofContext) -> ProofNode {
        let mut res1 = self.tactic1.action(data.clone(), context);

        let result = res1.eval();
        if result {
            return res1;
        } else {
            let res2 = self.tactic2.action(data, context);
            return ProofNode::new_or(res1, res2);
        }
    }
}

pub struct All<O, E, A> {
    enumerator: E,
    tactic: A,
    _phantom_data: PhantomData<O>,
}

pub fn all<O, E, A>(enumerator: E, tactic: A) -> All<O, E, A> {
    All {
        enumerator,
        tactic,
        _phantom_data: PhantomData,
    }
}

impl<E, A, I, O> Tactic<I> for All<O, E, A>
where
    E: Enumerator<I, O>,
    A: Tactic<O>,
{
    fn action(&self, data_in: I, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_all(self.enumerator.msg(&data_in));

        self.enumerator.iter(data_in, context).all(|d| {
            let item_msg = self.enumerator.item_msg(&d);
            let mut res = self.tactic.action(d, context);
            res = ProofNode::new_info(item_msg, res);
            let cont = res.eval();
            proof.add_child(res);
            cont
        });

        proof
    }
}

pub struct Any<O, E, A> {
    enumerator: E,
    tactic: A,
    _phantom_data: PhantomData<O>,
}

pub fn any<O, E, A>(enumerator: E, tactic: A) -> Any<O, E, A> {
    Any {
        enumerator,
        tactic,
        _phantom_data: PhantomData,
    }
}

impl<E, A, I, O> Tactic<I> for Any<O, E, A>
where
    E: Enumerator<I, O>,
    A: Tactic<O>,
{
    fn action(&self, data_in: I, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_any(self.enumerator.msg(&data_in));

        self.enumerator.iter(data_in, context).any(|d| {
            let item_msg = self.enumerator.item_msg(&d);
            let mut res = self.tactic.action(d, context);
            res = ProofNode::new_info(item_msg, res);
            let cont = res.eval();
            proof.add_child(res);
            cont
        });

        proof
    }
}

pub fn prove_nice_path_progress<C: CreditInvariant>(
    comps: Vec<Component>,
    credit_inv: C,
    output_dir: PathBuf,
    output_depth: usize,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    let c = credit_inv.complex_black(2);

    let path_length = 4;

    for last_comp in &comps {
        let context = ProofContext {
            credit_inv: DefaultCredits::new(c),
            path_len: path_length,
        };

        let mut proof = all(
            PathEnumerator,
            all(
                MatchingHitEnumerator::for_comp(path_length - 1),
                all(
                    NPCEnumerator,
                    or4(
                        LongerPathTactic,
                        ContractabilityTactic,
                        any(
                            ComponentHitEnumerator,
                            or(
                                LocalComplexMerge,
                                all(
                                    MatchingNodesEnumerator,
                                    all(
                                        NPCEnumerator,
                                        or(LocalMerge, LongerNicePathViaMatchingSwap),
                                    ),
                                ),
                            ),
                        ),
                        CycleMerge,
                    ),
                ),
            ),
        )
        .action(
            PathEnumeratorInput::new(last_comp.clone(), comps.clone()),
            &context,
        );

        let proved = proof.eval();

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
    }
}
