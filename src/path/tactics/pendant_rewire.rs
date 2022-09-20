use itertools::Itertools;

use crate::{
    path::{
        proof::{Statistics, Tactic},
        Matching3, MatchingEdge, PathHit, PathMatchingInstance, SelectedMatchingInstance,
        SuperNode,
    },
    proof_tree::ProofNode,
};

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

impl Tactic<SelectedMatchingInstance> for PendantRewireTactic {
    fn precondition(
        &self,
        data: &SelectedMatchingInstance,
        context: &crate::path::proof::ProofContext,
    ) -> bool {
        data.hit_comp_idx == context.path_len - 2 && data.matched.len() == 3
    }

    fn action(
        &mut self,
        data: &SelectedMatchingInstance,
        _context: &mut crate::path::proof::ProofContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let matching3 = &data.path_matching.matching;
        let other_matched = data
            .matched
            .iter()
            .filter(|e| e.1 != matching3.path_edge_left.unwrap().source())
            .collect_vec();

        let prelast = data.path_matching.path.nodes[data.hit_comp_idx].get_comp();
        let last = data.path_matching.path.last_comp();

        //if prelast.is_c6() || prelast.is_large() || prelast.is_complex() || prelast.is_c3() {
        if last.is_c3() || last.is_large() || last.is_c6() || last.is_c4() {
            let new_last_matching_edge = other_matched.first().unwrap();
            let new_matching = Matching3 {
                source_comp_idx: matching3.source_comp_idx,
                path_edge_left: Some(MatchingEdge(
                    new_last_matching_edge.1,
                    PathHit::Path(matching3.source_comp_idx - 1),
                )),
                path_edge_right: None,
                other_edges: vec![
                    MatchingEdge(
                        other_matched.last().unwrap().1,
                        PathHit::Path(matching3.source_comp_idx - 1),
                    ),
                    MatchingEdge(
                        matching3.path_edge_left.unwrap().source(),
                        PathHit::Path(matching3.source_comp_idx - 2),
                    ),
                ],
            };

            let mut path = data.path_matching.path.clone();
            let mut new_last = path.nodes.last().unwrap().get_zoomed().clone();
            new_last.in_node = Some(new_matching.path_edge_left.unwrap().source());
            *path.nodes.last_mut().unwrap() = SuperNode::Zoomed(new_last);

            let refer_to_instance = PathMatchingInstance {
                matching: new_matching,
                path,
            };

            self.num_proofs += 1;
            return ProofNode::new_leaf(
                format!(
                    "Rewire instance and reduce to path {} with matching {}.",
                    refer_to_instance.path, refer_to_instance.matching
                ),
                true,
            );
        }

        ProofNode::new_leaf(format!("Rewire not possible"), false)
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
