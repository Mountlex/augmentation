use std::fmt::Display;

use itertools::Itertools;

use crate::{
    path::{proof::PathContext, PseudoCycle, PseudoCycleInstance, SuperNode},
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
    Credit, CreditInv,
};

#[derive(Clone)]
pub struct CycleMergeTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl CycleMergeTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for CycleMergeTactic {
    fn print_stats(&self) {
        println!("Cycle merge {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<PseudoCycleInstance, PathContext> for CycleMergeTactic {
    fn action(&mut self, data: &PseudoCycleInstance, context: &PathContext) -> ProofNode {
        self.num_calls += 1;

        let mut cycle_value = data.pseudo_cycle.value(&context.credit_inv);

        if data
            .pseudo_cycle
            .nodes
            .iter()
            .any(|n| n.get_comp().is_complex())
        {
            // 2c due to gainful bridge covering. We convert the resulting complex to a large
            cycle_value += Credit::from_integer(2) * context.credit_inv.c
        }

        if cycle_value >= Credit::from_integer(2) {
            self.num_proofs += 1;
            ProofNode::new_leaf_success(
                format!("Merged pseudo cycle with value {}!", cycle_value),
                cycle_value == Credit::from_integer(2),
            )
        } else {
            ProofNode::new_leaf(
                format!(
                    "Failed cycle merge with value {}",
                    //data.pseudo_cycle,
                    cycle_value
                ),
                false,
            )
        }
    }
}

impl PseudoCycle {
    pub fn value(&self, credit_inv: &CreditInv) -> Credit {
        let first_complex = self
            .nodes
            .iter()
            .enumerate()
            .rev()
            .find(|(_, n)| n.get_comp().is_complex())
            .map(|(i, _)| i);

        self.nodes
            .iter()
            .enumerate()
            .map(|(j, node)| {
                let lower_complex = first_complex.is_some() && first_complex.unwrap() > j;

                match node {
                    SuperNode::Abstract(abs) => abs.value(credit_inv, lower_complex),
                    SuperNode::Zoomed(zoomed) => zoomed.value(credit_inv, lower_complex),
                    SuperNode::RemPath(_) => credit_inv.two_ec_credit(3) - Credit::from_integer(1),
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
