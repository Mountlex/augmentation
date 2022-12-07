use crate::{
    path::{proof::PathContext, AugmentedPathInstance, Pidx, SelectedHitInstance},
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

impl Tactic<AugmentedPathInstance, PathContext> for PendantRewireTactic {
    fn precondition(
        &self,
        data: &AugmentedPathInstance,
        _context: &crate::path::proof::PathContext,
    ) -> bool {
        data.fixed_edges_between(Pidx::Last, Pidx::Prelast).len() == 3 &&
        data.fixed_incident_edges(Pidx::Last).len() == 3 && data.nodes_with_abstract_edges(Pidx::Last).is_empty()
    }

    fn action(
        &mut self,
        _data: &AugmentedPathInstance,
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
