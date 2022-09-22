use crate::{
    path::{
        proof::{or, ProofContext, Statistics, Tactic},
        AugmentedPathInstance, MatchingEdge,
    },
    proof_tree::ProofNode,
};

pub struct LongerPathTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl LongerPathTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for LongerPathTactic {
    fn print_stats(&self) {
        println!("Longer path {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<AugmentedPathInstance> for LongerPathTactic {
    fn action(
        &mut self,
        data: &AugmentedPathInstance,
        context: &mut ProofContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let outside_hits = data.outside_hits();
        let mut proof = if outside_hits.len() == 2 {
            or(
                LongerNicePathCheck::check_for(&outside_hits[0]),
                LongerNicePathCheck::check_for(&outside_hits[1]),
            )
            .action(data, context)
        } else if outside_hits.len() == 1 {
            LongerNicePathCheck::check_for(&outside_hits[0]).action(data, context)
        } else {
            panic!()
        };
        if proof.eval().success() {
            self.num_proofs += 1;
        }
        proof
    }

    fn precondition(&self, data: &AugmentedPathInstance, _context: &ProofContext) -> bool {
        !data.outside_hits().is_empty()
    }
}

// Private tactics (subroutines)

struct LongerNicePathCheck<'a> {
    other_matching_edge: &'a MatchingEdge,
}

impl<'a> LongerNicePathCheck<'a> {
    fn check_for(other_matching_edge: &'a MatchingEdge) -> Self {
        LongerNicePathCheck {
            other_matching_edge,
        }
    }
}

impl<'a> Tactic<AugmentedPathInstance> for LongerNicePathCheck<'a> {
    fn action(
        &mut self,
        data: &AugmentedPathInstance,
        _context: &mut ProofContext,
    ) -> crate::proof_tree::ProofNode {
        let last = data.path.nodes.last().unwrap().get_zoomed();
        let last_comp = last.get_comp();

        if last_comp.is_c6()
            || last_comp.is_large()
            || last
                .npc
                .is_nice_pair(last.in_node.unwrap(), self.other_matching_edge.source())
        {
            ProofNode::new_leaf(
                format!(
                    "Longer nice path found via edge ({})!",
                    self.other_matching_edge
                ),
                true,
            )
        } else {
            ProofNode::new_leaf(
                format!(
                    "No longer nice path possible via edge ({})!",
                    self.other_matching_edge
                ),
                false,
            )
        }
    }

    fn precondition(&self, _data: &AugmentedPathInstance, _context: &ProofContext) -> bool {
        true
    }
}
