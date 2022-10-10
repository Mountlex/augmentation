use crate::{
    path::{
        proof::PathContext,
        tactics::{cycle_merge::CycleMergeTactic, cycle_rearrange::CycleRearrangeTactic},
        CycleEdge, PathHit, Pidx, PseudoCycle, PseudoCycleInstance, SelectedHitInstance,
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
        _context: &crate::path::proof::PathContext,
    ) -> bool {
        data.hit_comp_idx.is_prelast()
            && data
                .instance
                .fixed_edges_between(Pidx::Last, Pidx::Prelast)
                .len()
                == 2
            && data
                .instance
                .non_path_matching_edges
                .iter()
                .any(|m| matches!(m.hit(), PathHit::Path(i) if i >= 2.into()))
    }

    fn action(
        &mut self,
        data: &SelectedHitInstance,
        context: &crate::path::proof::PathContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let matched = data.instance.fixed_edges_between(Pidx::Last, Pidx::Prelast);

        let m_path = data.instance.path_edge(Pidx::Last).unwrap();
        let m_other = matched.iter().find(|e| m_path != **e).unwrap().clone();

        let mut new_instance = data.clone();
        new_instance.instance.swap_path_edge(m_other, Pidx::Last);

        //dbg!(&new_instance);
        let path_hit = new_instance
            .instance
            .non_path_matching_edges
            .iter()
            .find(|e| matches!(e.hit(), PathHit::Path(i) if i >= 2.into()))
            .unwrap();

        let hit_idx = path_hit.hits_path().unwrap();

        // Build new cycle
        let mut pseudo_nodes = new_instance
            .instance
            .nodes
            .split_at(hit_idx.raw() + 1)
            .0
            .to_vec();

        // Set in and out for matching edge

        // set out of first node
        pseudo_nodes
            .first_mut()
            .unwrap()
            .get_zoomed_mut()
            .set_out(path_hit.source());

        // the last node in the cycle is still abstract, so there might be no nice pair now!
        pseudo_nodes
            .last_mut()
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
            path_hit_idx: hit_idx,
        };

        let mut proof = or(CycleMergeTactic::new(), CycleRearrangeTactic::new())
            .action(&cycle_instance, context);
        if proof.eval().success() {
            self.num_proofs += 1;
        }
        return proof;
    }
}
