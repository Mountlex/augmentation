use crate::{
    local_merge::prove_via_direct_merge,
    path::{
        proof::{ProofContext, Statistics, Tactic},
        utils::get_local_merge_graph,
        SelectedHitInstance,
    },
    proof_tree::ProofNode,
};

pub struct LocalComplexMerge {
    num_calls: usize,
    num_proofs: usize,
}

impl LocalComplexMerge {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for LocalComplexMerge {
    fn print_stats(&self) {
        println!(
            "Local complex merge {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}

impl Tactic<SelectedHitInstance> for LocalComplexMerge {
    fn action(&mut self, data: &SelectedHitInstance, context: &ProofContext) -> ProofNode {
        self.num_calls += 1;

        let left_comp = data.instance.path.nodes[data.hit_comp_idx].get_comp();
        let last_comp_ref = data.instance.path.last_comp();

        let matched = data.instance.matching_edges_hit(data.hit_comp_idx);
        assert!(matched.len() == 1);

        let right_match = matched.first().unwrap().source();
        // only try complex merges

        let complex_merge = left_comp.graph().nodes().all(|left_match| {
            let graph_with_matching =
                get_local_merge_graph(left_comp, last_comp_ref, &vec![(left_match, right_match)]);

            prove_via_direct_merge(
                &graph_with_matching,
                vec![left_comp, last_comp_ref],
                context.credit_inv.clone(),
                &mut ProofNode::new_any(String::new()),
            )
        });

        if complex_merge {
            self.num_proofs += 1;
            return ProofNode::new_leaf(format!("Complex Merge possible"), true);
        } else {
            return ProofNode::new_leaf(format!("Complex Merge failed"), false);
        }
    }

    fn precondition(&self, data: &SelectedHitInstance, _context: &ProofContext) -> bool {
        let left_comp = data.instance.path.nodes[data.hit_comp_idx].get_comp();
        let last_comp_ref = data.instance.path.last_comp();
        let matched = data.instance.matching_edges_hit(data.hit_comp_idx);

        left_comp.is_complex() && last_comp_ref.is_complex() && matched.len() == 1
    }
}
