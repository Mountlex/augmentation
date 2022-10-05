use crate::{
    path::{proof::PathContext, Pidx, SelectedHitInstance},
    proof_logic::{Statistics, Tactic},
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

impl Tactic<SelectedHitInstance, PathContext> for PendantRewireTactic {
    fn precondition(
        &self,
        data: &SelectedHitInstance,
        _context: &crate::path::proof::PathContext,
    ) -> bool {
        data.hit_comp_idx.is_prelast()
            && data
                .instance
                .fixed_edges_between(Pidx::Last, Pidx::Prelast)
                .len()
                == 3
    }

    fn action(
        &mut self,
        _data: &SelectedHitInstance,
        _context: &crate::path::proof::PathContext,
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
