use crate::{
    path::{
        proof::PathContext,
        tactics::{cycle_merge::CycleMergeTactic, cycle_rearrange::CycleRearrangeTactic},
        CycleEdge, PathHit, PseudoCycle, PseudoCycleInstance, SelectedHitInstance,
    },
    proof_logic::{or, Statistics, Tactic},
};

#[derive(Clone)]
pub struct CycleMergeViaSwap {
    num_calls: usize,
    num_proofs: usize,
}

impl CycleMergeViaSwap {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for CycleMergeViaSwap {
    fn print_stats(&self) {
        println!(
            "Cycle merges via matching swap {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}

impl Tactic<SelectedHitInstance, PathContext> for CycleMergeViaSwap {
    fn precondition(
        &self,
        data: &SelectedHitInstance,
        context: &crate::path::proof::PathContext,
    ) -> bool {
        data.hit_comp_idx == context.path_len - 2
            && data
                .instance
                .fixed_edges_between(context.path_len - 2, context.path_len - 1)
                .len()
                == 2
            && data
                .instance
                .non_path_matching_edges
                .iter()
                .any(|m| matches!(m.hit(), PathHit::Path(i) if i <= context.path_len - 3))
    }

    fn action(
        &mut self,
        data: &SelectedHitInstance,
        context: &crate::path::proof::PathContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let matched = data
            .instance
            .fixed_edges_between(context.path_len - 2, context.path_len - 1);

        let m_path = data.instance.path_edge(context.path_len - 1).unwrap();
        let m_other = matched.iter().find(|e| m_path != **e).unwrap().clone();

        let mut new_instance = data.clone();
        new_instance
            .instance
            .swap_path_edge(m_other, context.path_len - 1);

        //dbg!(&new_instance);
        let path_hit = new_instance
            .instance
            .non_path_matching_edges
            .iter()
            .find(|e| matches!(e.hit(), PathHit::Path(i) if i <= context.path_len - 3))
            .unwrap();

        // Build new cycle
        let mut pseudo_nodes = new_instance
            .instance
            .path
            .nodes
            .split_at(path_hit.hits_path().unwrap())
            .1
            .to_vec();

        // Set in and out for matching edge
        pseudo_nodes.last_mut().unwrap().get_zoomed_mut().out_node = Some(path_hit.source());
        pseudo_nodes
            .first_mut()
            .unwrap()
            .get_abstract_mut()
            .nice_pair = false;

        let cycle = PseudoCycle {
            nodes: pseudo_nodes,
        };
        let cycle_instance = PseudoCycleInstance {
            cycle_edge: CycleEdge::Matching(path_hit.clone()),
            path_matching: new_instance.instance,
            pseudo_cycle: cycle,
        };

        let mut proof = or(
            CycleMergeTactic::new(),
            //DoubleCycleMergeTactic::new(),
            CycleRearrangeTactic::new(),
        )
        .action(&cycle_instance, context);
        if proof.eval().success() {
            self.num_proofs += 1;
        }
        return proof;
    }
}
