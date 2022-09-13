use crate::{
    path::{
        proof::{or, ProofContext, Tactic},
         MatchingEdge, PathMatchingInstance,
    },
    proof_tree::ProofNode,
};

pub struct LongerPathTactic;

impl Tactic<PathMatchingInstance> for LongerPathTactic {
    fn action(
        &self,
        data: PathMatchingInstance,
        context: &ProofContext,
    ) -> crate::proof_tree::ProofNode {
        let outside_hits = data.matching.outside_hits();
        if outside_hits.len() == 2 {
            or(
                LongerNicePathCheck::check_for(&outside_hits[0]),
                LongerNicePathCheck::check_for(&outside_hits[1]),
            )
            .action(data, context)
        } else if outside_hits.len() == 1 {
            LongerNicePathCheck::check_for(&outside_hits[0]).action(data, context)
        } else {
            ProofNode::new_leaf(format!("None of the matching edges hits outside"), false)
        }
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

impl<'a> Tactic<PathMatchingInstance> for LongerNicePathCheck<'a> {
    fn action(
        &self,
        data: PathMatchingInstance,
        _context: &ProofContext,
    ) -> crate::proof_tree::ProofNode {
        let last = data.path.nodes.last().unwrap().to_zoomed();
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
}
