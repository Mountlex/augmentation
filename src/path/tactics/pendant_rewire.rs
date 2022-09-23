use crate::{
    path::{
        proof::{Statistics, Tactic},
        SelectedHitInstance,
    },
    proof_tree::ProofNode,
};

#[derive(Clone)]
pub struct PendantRewireTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl PendantRewireTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Tactic<SelectedHitInstance> for PendantRewireTactic {
    fn precondition(
        &self,
        data: &SelectedHitInstance,
        context: &crate::path::proof::ProofContext,
    ) -> bool {
        data.hit_comp_idx == context.path_len - 2
            && data
                .instance
                .fixed_edges_between(context.path_len - 2, context.path_len - 1)
                .len()
                == 3
    }

    fn action(
        &mut self,
        _data: &SelectedHitInstance,
        _context: &crate::path::proof::ProofContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        return ProofNode::new_leaf(format!("Rewire pendant node!",), true);
    }
}

impl Statistics for PendantRewireTactic {
    fn print_stats(&self) {
        println!(
            "Rewired pendant nodes {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}
