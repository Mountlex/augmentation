use itertools::Itertools;

use crate::{
    path::{
        proof::{ProofContext, Statistics, Tactic},
        utils::hamiltonian_paths,
        SelectedMatchingInstance,
    },
    proof_tree::ProofNode,
};

pub struct LongerNicePathViaMatchingSwap {
    num_calls: usize,
    num_proofs: usize,
}

impl LongerNicePathViaMatchingSwap {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for LongerNicePathViaMatchingSwap {
    fn print_stats(&self) {
        println!(
            "Longer nice path via matching swap {} / {}",
            self.num_proofs, self.num_calls
        );
    }
}

impl Tactic<SelectedMatchingInstance> for LongerNicePathViaMatchingSwap {
    fn action(&mut self, data: SelectedMatchingInstance, context: &mut ProofContext) -> ProofNode {
        self.num_calls += 1;

        let three_matching = data.path_matching.matching;
        let matched = data.matched;

        let outside_hits = three_matching.outside_hits();

        let last = data.path_matching.path.nodes.last().unwrap().to_zoomed();
        let prelast = data.path_matching.path.nodes[context.path_len - 2].to_zoomed();
        let last_comp = last.get_comp();
        let prelast_comp = prelast.get_comp();

        let m_outside = outside_hits[0];

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

        // If matching edge swap cannot be a nice path
        if (last_comp.is_c3() || last_comp.is_c4() || last_comp.is_c5() || last_comp.is_complex())
            && !last.npc.is_nice_pair(m_other.1, m_outside.source())
        {
            return ProofNode::new_leaf(
                "No longer path via swapping matching edges: no nice pairs".into(),
                false,
            );
        }

        // Now if C_l-1 does not care about nice pairs, we are done!
        if prelast_comp.is_c6() || prelast_comp.is_large() {
            self.num_proofs += 1;
            return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true);
        }

        // For others, we have to check that swaping the path edges keeps a nice pair
        if prelast_comp
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
        {
            self.num_proofs += 1;
            return ProofNode::new_leaf("Longer path via swapping matching edges".into(), true);
        }
        return ProofNode::new_leaf(
            "No longer path via swapping matching edges: no swapping".into(),
            false,
        );
    }

    fn precondition(&self, data: &SelectedMatchingInstance, context: &ProofContext) -> bool {
        let outside_hits = data.path_matching.matching.outside_hits();
        data.matched.len() == 2
            && outside_hits.len() == 1
            && data.hit_comp_idx == context.path_len - 2
    }
}
