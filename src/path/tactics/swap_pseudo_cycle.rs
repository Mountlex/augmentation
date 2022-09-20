use itertools::Itertools;

use crate::{
    path::{
        proof::{or, FilterMapTactic, Statistics, Tactic},
        tactics::{cycle_merge::CycleMerge, cycle_rearrange::CycleRearrangeTactic},
        utils::hamiltonian_paths,
        MatchingEdge, PathHit, PseudoCycle, PseudoCycleInstance, SelectedMatchingInstance,
        SuperNode, AbstractNode,
    },
    proof_tree::ProofNode,
};

pub struct SwapPseudoCycleEdgeTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl SwapPseudoCycleEdgeTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for SwapPseudoCycleEdgeTactic {
    fn print_stats(&self) {
        println!(
            "Cycle merges via matching swap {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}

impl Tactic<SelectedMatchingInstance> for SwapPseudoCycleEdgeTactic {
    fn precondition(
        &self,
        data: &SelectedMatchingInstance,
        context: &crate::path::proof::ProofContext,
    ) -> bool {
        data.hit_comp_idx == context.path_len - 2
            && data.matched.len() == 2
            && data.path_matching.matching.outside_hits().is_empty()
    }

    fn action(
        &mut self,
        data: &SelectedMatchingInstance,
        context: &mut crate::path::proof::ProofContext,
    ) -> crate::proof_tree::ProofNode {
        self.num_calls += 1;

        let three_matching = &data.path_matching.matching;
        let matched = &data.matched;

        let path_hit = three_matching
            .other_edges
            .iter()
            .find(|e| matches!(e.hit(), PathHit::Path(i) if i <= context.path_len - 3))
            .unwrap();

        let last = data.path_matching.path.nodes.last().unwrap().to_zoomed();
        let prelast = data.path_matching.path.nodes[context.path_len - 2].to_zoomed();
        let last_comp = last.get_comp();
        let prelast_comp = prelast.get_comp();

        let m_path = matched
            .iter()
            .find(|e| three_matching.path_edge_left.unwrap().source() == e.1)
            .unwrap()
            .clone();
        let m_other = matched
            .iter()
            .find(|e| three_matching.path_edge_left.unwrap().source() != e.1)
            .unwrap()
            .clone();

        let prelast_np = if (prelast_comp.is_c3() || prelast_comp.is_c4() || (prelast_comp.is_c5() && !prelast.used)) {

        prelast_comp
                .graph()
                .nodes()
                .filter(|left_in| *left_in != m_path.0)
                .all(|left_in| {
                    // for any left_in, we consider all possible hamiltonian paths for the current nice pair
                    hamiltonian_paths(left_in, m_path.0, &prelast_comp.nodes())
                        .into_iter()
                        .all(|ham_path| {
                            let edges = ham_path
                                .windows(2)
                                .map(|e| (e[0], e[1]))
                                .chain(prelast_comp.edges().into_iter())
                                .collect_vec();

                            // If for every such path, a nice pair using _any_ hamiltonian path for left_in and the new path edge endpoint is possible, it must be a nice pair
                            hamiltonian_paths(left_in, m_other.0, &prelast_comp.nodes())
                                .into_iter()
                                .any(|path| {
                                    path.windows(2).map(|e| (e[0], e[1])).all(|(u, v)| {
                                        edges.contains(&(u, v)) || edges.contains(&(v, u))
                                    })
                                })
                        })
                })
            
            } else {
                false
            };
        

        // Build new cycle

        let mut pseudo_nodes = data
            .path_matching
            .path
            .nodes
            .split_at(path_hit.hits_path().unwrap())
            .1
            .to_vec();

        let length = pseudo_nodes.len();

        assert!(matches!(
            pseudo_nodes.last(),
            Some(SuperNode::Zoomed(_))
        ));
        assert!(matches!(
            pseudo_nodes.first(),
            Some(SuperNode::Abstract(_))
        ));

        if let Some(SuperNode::Zoomed(zoomed)) = pseudo_nodes.last_mut() {
            zoomed.out_node = Some(path_hit.source());
            zoomed.in_node = Some(m_other.1)
        }

        let prelast_node = pseudo_nodes.get_mut(length - 2).unwrap();
        *prelast_node = SuperNode::Abstract(AbstractNode {
            comp: prelast_node.get_comp().clone(),
            in_not_out: true,
            nice_pair: prelast_np,
            used: prelast.used,
        });

        assert!(matches!(
            pseudo_nodes.get(length - 2),
            Some(SuperNode::Abstract(_))
        ));

        if let Some(SuperNode::Abstract(abs)) = pseudo_nodes.first_mut() {
            abs.nice_pair = false
        }
        let cycle = PseudoCycle {
            nodes: pseudo_nodes,
        };
        let cycle_instance = PseudoCycleInstance {
            path_matching: data.path_matching.clone(),
            cycle_edge: path_hit.clone(),
            pseudo_cycle: cycle,
        };

        let mut proof = or(CycleMerge::new(), CycleRearrangeTactic::new()).action(&cycle_instance, context);
        if proof.eval().success() {
            self.num_proofs += 1;
        }
        return proof
    }
}
