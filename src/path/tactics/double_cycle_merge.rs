use crate::{
    path::{
        proof::{Statistics, Tactic},
        PseudoCycleInstance, SuperNode,
    },
    proof_tree::ProofNode,
    Credit,
};

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

impl Tactic<PseudoCycleInstance> for DoubleCycleMergeTactic {
    fn precondition(
        &self,
        data: &PseudoCycleInstance,
        context: &crate::path::proof::ProofContext,
    ) -> bool {
        data.cycle_edge.hits_path().unwrap() == context.path_len - 3
            && data.pseudo_cycle.nodes.first().unwrap().get_comp().is_c3()
    }

    fn action(
        &mut self,
        data: &PseudoCycleInstance,
        context: &mut crate::path::proof::ProofContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let mut cycle = data.pseudo_cycle.clone();
        cycle
            .nodes
            .insert(1, data.path_matching.path.nodes.first().unwrap().clone());

        // if prelast is a C3, we can guarantee that there is a nice pair
        let prelast_np = cycle.nodes.get(2).unwrap().get_comp().is_c3();

        cycle.nodes.get_mut(0).unwrap().get_abstract_mut().nice_pair = true;
        cycle.nodes.get_mut(1).unwrap().get_abstract_mut().nice_pair = false;
        cycle.nodes.get_mut(2).unwrap().get_abstract_mut().nice_pair = prelast_np;

        let cycle_value = cycle.value(context.credit_inv.clone());
        if cycle_value >= Credit::from_integer(2) {
            self.num_proofs += 1;
            ProofNode::new_leaf_success(
                format!(
                    "Merged double pseudo cycle {} with value {}!",
                    cycle, cycle_value
                ),
                cycle_value == Credit::from_integer(2),
            )
        } else {
            ProofNode::new_leaf(
                format!(
                    "Failed double cycle merge {} with value {}",
                    cycle, cycle_value
                ),
                false,
            )
        }
    }
}
