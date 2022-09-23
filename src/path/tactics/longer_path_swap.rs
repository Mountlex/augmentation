use crate::{
    path::{
        proof::{ProofContext, Statistics, Tactic},
        SelectedHitInstance,
    },
    proof_tree::ProofNode,
};

#[derive(Clone)]
pub struct LongerPathViaSwap {
    num_calls: usize,
    num_proofs: usize,
}

impl LongerPathViaSwap {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for LongerPathViaSwap {
    fn print_stats(&self) {
        println!(
            "Longer nice path via matching swap {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}

impl Tactic<SelectedHitInstance> for LongerPathViaSwap {
    fn action(&mut self, data: &SelectedHitInstance, context: &ProofContext) -> ProofNode {
        self.num_calls += 1;

        let matched = data
            .instance
            .fixed_edges_between(context.path_len - 2, context.path_len - 1);
        let outside_hits = data.instance.outside_hits();

        let last = data.instance.path.nodes.last().unwrap().get_zoomed();
        let prelast = data.instance.path[context.path_len - 2].get_zoomed();
        let last_comp = last.get_comp();
        let prelast_comp = prelast.get_comp();

        let m_outside = outside_hits[0];

        let m_path = data.instance.path_edge(context.path_len - 1).unwrap();
        let m_other = matched.iter().find(|e| m_path.1 != e.1).unwrap().clone();

        // If matching edge swap cannot be a nice path
        if (last_comp.is_c3()
            || last_comp.is_c4()
            || (last_comp.is_c5() && !last.used)
            || last_comp.is_complex())
            && !last.npc.is_nice_pair(m_other.1, m_outside.source())
        {
            return ProofNode::new_leaf(
                "No longer path via swapping matching edges: no nice pairs".into(),
                false,
            );
        }

        // Now if C_l-1 does not care about nice pairs, we are done!
        if prelast_comp.is_c6() || prelast_comp.is_large() || prelast_comp.is_c5() {
            self.num_proofs += 1;
            return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true);
        }

        let left_in = prelast.in_node.unwrap();

        // Check if new path edge still ensures nice pair property of prelast
        if prelast.npc.is_nice_pair(left_in, m_other.0) {
            self.num_proofs += 1;
            return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true);
        }
        return ProofNode::new_leaf(
            "No longer path via swapping matching edges: no swapping".into(),
            false,
        );
    }

    fn precondition(&self, data: &SelectedHitInstance, context: &ProofContext) -> bool {
        let outside_hits = data.instance.outside_hits();
        data.instance
            .fixed_edges_between(context.path_len - 2, context.path_len - 1)
            .len()
            == 2
            && outside_hits.len() == 1
            && data.hit_comp_idx == context.path_len - 2
    }
}
