 use crate::path::{SelectedMatchingInstance, proof::Tactic};





pub struct PendantRewireTactic;

impl Tactic<SelectedMatchingInstance> for PendantRewireTactic {
    fn precondition(&self, data: &SelectedMatchingInstance, context: &crate::path::proof::ProofContext) -> bool {
        data.hit_comp_idx == context.path_len - 2 && data.matched.len() == 2
    }

    fn action(&mut self, data: &SelectedMatchingInstance, context: &mut crate::path::proof::ProofContext) -> crate::proof_tree::ProofNode {
        
        panic!()
    }
}
