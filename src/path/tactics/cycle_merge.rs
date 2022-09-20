use std::fmt::Display;

use itertools::Itertools;

use crate::{
    comps::CreditInvariant,
    path::{
        proof::{ProofContext, Statistics, Tactic},
        PseudoCycle,
        PseudoCycleInstance, SuperNode,
    },
    proof_tree::ProofNode,
    Credit,
};

pub struct CycleMerge {
    num_calls: usize,
    num_proofs: usize,
}

impl CycleMerge {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for CycleMerge {
    fn print_stats(&self) {
        println!("Cycle merge {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<PseudoCycleInstance> for CycleMerge {
    fn action(&mut self, data: &PseudoCycleInstance, context: &mut ProofContext) -> ProofNode {
        self.num_calls += 1;

        let cycle_value = data.pseudo_cycle.value(context.credit_inv.clone());
        if cycle_value >= Credit::from_integer(2) {
            self.num_proofs += 1;
            ProofNode::new_leaf_success(
                format!("Merged pseudo cycle with value {}!", cycle_value),
                cycle_value == Credit::from_integer(2),
            )
        } else {
            ProofNode::new_leaf(
                format!("Failed cycle merge with value {}", cycle_value),
                false,
            )
        }
    }

    fn precondition(&self, _data: &PseudoCycleInstance, _context: &ProofContext) -> bool {
        // If we land here, we want that at least one matching edge hits C_j for j <= l - 2.
        true
    }
}


impl PseudoCycle {
    fn value<C: CreditInvariant>(&self, credit_inv: C) -> Credit {
        let first_complex = self
            .nodes
            .iter()
            .enumerate()
            .find(|(_, n)| n.get_comp().is_complex())
            .map(|(i, _)| i);

        self.nodes
            .iter()
            .enumerate()
            .map(|(j, node)| {
                let lower_complex = first_complex.is_some() && first_complex.unwrap() < j;

                match node {
                    SuperNode::Abstract(abs) => abs.value(credit_inv.clone(), lower_complex),
                    SuperNode::Zoomed(zoomed) => zoomed.value(credit_inv.clone(), lower_complex),
                }
            })
            .sum()
    }
}

impl Display for PseudoCycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        write!(
            f,
            "{}",
            self.nodes
                .iter()
                .map(|node| format!("{}", node))
                .join(" -- ")
        )?;
        write!(f, "]")
    }
}
