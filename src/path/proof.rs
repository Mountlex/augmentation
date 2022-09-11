use std::fmt::Write;
use std::{marker::PhantomData, path::PathBuf};

use crate::{
    comps::{Component, CreditInvariant, DefaultCredits},
    proof_tree::ProofNode,
};

use super::enumerators::comp_hits::{ComponentHitEnumerator, ComponentHitOutput};
use super::enumerators::matching_hits::{MatchingHitEnumerator, MatchingHitEnumeratorOutput};
use super::enumerators::matching_nodes::{MatchingNodesEnumerator, MatchingNodesEnumeratorOutput};
use super::enumerators::nice_pairs::{NPCEnumOutput, NPCEnumerator};
use super::enumerators::nice_paths::{PathEnumerator, PathEnumeratorInput};
use super::tactics::complex_merge::LocalComplexMerge;
use super::tactics::cycle_merge::CycleMerge;
use super::tactics::local_merge::LocalMerge;
use super::tactics::longer_path::LongerPathTactic;
use super::tactics::longer_path_swap::LongerNicePathViaMatchingSwap;

pub struct ProofContext {
    pub credit_inv: DefaultCredits,
    pub path_len: usize,
}

pub trait Enumerator {
    type In;
    type Out;
    //type Iter: Iterator<Item = Self::Out>;

    fn msg(&self, data_in: &Self::In) -> String;

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>>;

    fn item_msg(&self, item: &Self::Out) -> String {
        String::new()
    }
}

pub trait Tactic {
    type In;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode;
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
    Or {
        tactic1,
        tactic2: or(tactic2, tactic3),
        _phantom_data: PhantomData,
    }
}

impl<I, A1, A2> Tactic for Or<I, A1, A2>
where
    A1: Tactic,
    A2: Tactic,
    A1::In: From<I>,
    A2::In: From<I>,
    I: Clone,
{
    type In = I;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        let mut res1 = self.tactic1.action(data.clone().into(), context);
        
        let result = res1.eval();
        if result {
            return res1
        } else {
            let res2 = self.tactic2.action(data.into(), context);
            return  ProofNode::new_or(res1, res2);
        }
    }
}

pub struct All<E, A> {
    enumerator: E,
    tactic: A,
}

pub fn all<E, A>(enumerator: E, tactic: A) -> All<E, A> {
    All { enumerator, tactic }
}

impl<E, A> Tactic for All<E, A>
where
    E: Enumerator,
    A: Tactic,
    A::In: From<E::Out>,
{
    type In = E::In;

    fn action(&self, data_in: Self::In, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_all(self.enumerator.msg(&data_in));

        self.enumerator.iter(data_in).all(|d| {
            let item_msg = self.enumerator.item_msg(&d);
            let mut res = self.tactic.action(d.into(), context);
            res = ProofNode::new_info(item_msg, res);
            let cont = res.eval();
            proof.add_child(res);
            cont
        });

        proof
    }
}

pub struct Any<E, A> {
    enumerator: E,
    tactic: A,
}

pub fn any<E, A>(enumerator: E, tactic: A) -> Any<E, A> {
    Any { enumerator, tactic }
}

impl<E, A> Tactic for Any<E, A>
where
    E: Enumerator,
    A: Tactic,
    A::In: From<E::Out>,
{
    type In = E::In;

    fn action(&self, data_in: Self::In, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_any(self.enumerator.msg(&data_in));

        self.enumerator.iter(data_in).any(|d| {
            let item_msg = self.enumerator.item_msg(&d);
            let mut res = self.tactic.action(d.into(), context);
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
                MatchingHitEnumerator,
                all(
                    NPCEnumerator::new(),
                    or3::<NPCEnumOutput<MatchingHitEnumeratorOutput>, _, _, _>(
                        LongerPathTactic,
                        any(
                            ComponentHitEnumerator,
                            or::<ComponentHitOutput, _, _>(
                                LocalComplexMerge,
                                all(
                                    MatchingNodesEnumerator,
                                    all(
                                        NPCEnumerator::new(),
                                        or::<NPCEnumOutput<MatchingNodesEnumeratorOutput>, _, _>(
                                            LocalMerge,
                                            LongerNicePathViaMatchingSwap,
                                        ),
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
