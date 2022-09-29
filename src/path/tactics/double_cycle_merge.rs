use itertools::Itertools;

use crate::{
    path::{proof::PathContext, AugmentedPathInstance, PseudoCycle},
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
    Credit,
};

#[derive(Clone)]
pub struct DoubleCycleMergeTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl DoubleCycleMergeTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for DoubleCycleMergeTactic {
    fn print_stats(&self) {
        println!(
            "Double cycle merge {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}

impl Tactic<AugmentedPathInstance, PathContext> for DoubleCycleMergeTactic {
    fn precondition(&self, data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        data.fixed_edges_between(0, 2).len() > 0 && data.fixed_edges_between(1, 3).len() > 0
    }

    fn action(
        &mut self,
        data: &AugmentedPathInstance,
        context: &PathContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;
        let left_cycle_edges = data.fixed_edges_between(0, 2);
        let right_cycle_edges = data.fixed_edges_between(1, 3);

        for left_cycle_edge in &left_cycle_edges {
            for right_cycle_edge in &right_cycle_edges {
                let mut cycle_nodes = vec![
                    data.path[0].clone(),
                    data.path[2].clone(),
                    data.path[3].clone(),
                    data.path[1].clone(),
                ];


                let n = cycle_nodes[0].get_zoomed().out_node.unwrap();
                cycle_nodes[0].get_zoomed_mut().set_in(n);
                cycle_nodes[0].get_zoomed_mut().set_out(left_cycle_edge.0);

                cycle_nodes[1].get_zoomed_mut().set_in(left_cycle_edge.1);

                cycle_nodes[2].get_zoomed_mut().set_out(right_cycle_edge.1);

                let n = cycle_nodes[3].get_zoomed().in_node.unwrap();
                cycle_nodes[3].get_zoomed_mut().set_out(n);
                cycle_nodes[3].get_zoomed_mut().set_in(right_cycle_edge.0);

                let cycle = PseudoCycle { nodes: cycle_nodes };

                let cycle_value = cycle.value(&context.credit_inv);
                if cycle_value >= Credit::from_integer(2) {
                    self.num_proofs += 1;
                    return ProofNode::new_leaf_success(
                        format!("Merged double pseudo"),
                        cycle_value == Credit::from_integer(2),
                    );
                }
            }
        }
        ProofNode::new_leaf(
            format!(
                "Failed double cycle merge using edges {} and {}",
                left_cycle_edges.into_iter().join(", "),
                right_cycle_edges.into_iter().join(", ")
            ),
            false,
        )
    }
}
