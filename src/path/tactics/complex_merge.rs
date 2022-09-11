use crate::{
    comps::Node,
    local_merge::prove_via_direct_merge,
    path::{
        enumerators::comp_hits::ComponentHitOutput,
        proof::{ProofContext, Tactic},
        utils::get_local_merge_graph,
        NicePairConfig, NicePath,
    },
    proof_tree::ProofNode,
};

impl From<ComponentHitOutput> for LocalComplexMergeInput {
    fn from(o: ComponentHitOutput) -> Self {
        LocalComplexMergeInput {
            path: o.path,
            npc_last: o.npc_last,
            hit_comp_idx: o.hit_comp_idx,
            right_matched: o.right_matched,
        }
    }
}

pub struct LocalComplexMergeInput {
    pub path: NicePath,
    pub npc_last: NicePairConfig,
    pub hit_comp_idx: usize,
    pub right_matched: Vec<Node>,
}

pub struct LocalComplexMerge;

impl Tactic for LocalComplexMerge {
    type In = LocalComplexMergeInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        let left_comp = data.path.nodes[data.hit_comp_idx].get_comp();
        let last_comp_ref = data.path.nodes.last().unwrap().get_comp();

        if data.right_matched.len() == 1 {
            let right_match = *data.right_matched.first().unwrap();
            // only try complex merges

            let complex_merge = left_comp.graph().nodes().all(|left_match| {
                let graph_with_matching = get_local_merge_graph(
                    left_comp,
                    last_comp_ref,
                    &vec![(left_match, right_match)],
                );

                prove_via_direct_merge(
                    &graph_with_matching,
                    vec![left_comp, last_comp_ref],
                    context.credit_inv.clone(),
                    &mut ProofNode::new_any(String::new()),
                )
            });

            if complex_merge {
                return ProofNode::new_leaf(format!("Complex Merge possible"), true);
            }
        }
        return ProofNode::new_leaf(format!("Complex Merge failed"), false);
    }
}
