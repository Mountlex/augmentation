use crate::{
    comps::CreditInvariant,
    path::{
        enumerators::{matching_hits::MatchingHitEnumeratorOutput, nice_pairs::NPCEnumOutput},
        proof::{ProofContext, Tactic},
        NicePairConfig, NicePath, PathMatchingEdge, PathMatchingHits, PseudoCycle, SuperNode,
        ThreeMatching, ZoomedNode,
    },
    proof_tree::ProofNode,
    Credit,
};

impl From<NPCEnumOutput<MatchingHitEnumeratorOutput>> for CycleMergeInput {
    fn from(o: NPCEnumOutput<MatchingHitEnumeratorOutput>) -> Self {
        CycleMergeInput {
            path: o.input.nice_path,
            m_last: o.input.three_matching,
            np_config_last: o.npc,
        }
    }
}

pub struct CycleMergeInput {
    path: NicePath,
    m_last: ThreeMatching,
    np_config_last: NicePairConfig,
}

pub struct CycleMerge;

impl Tactic for CycleMerge {
    type In = CycleMergeInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        // If we land here, we want that at least one matching edge hits C_j for j <= l - 2.
        if !(matches!(data.m_last.1.hit(), PathMatchingHits::Path(j) if j <= context.path_len - 3)
            || matches!(data.m_last.2.hit(), PathMatchingHits::Path(j) if j <= context.path_len - 3))
        {
            return ProofNode::new_leaf(
                format!("There are no matching edges forming cycles! Aborting"),
                false,
            );
        }

        let mut case_path = data.path.clone();
        *case_path.nodes.last_mut().unwrap() = SuperNode::Zoomed(ZoomedNode {
            comp: case_path.nodes.last().unwrap().get_comp().clone(),
            in_node: Some(data.m_last.0.source()),
            out_node: None,
            npc: data.np_config_last.clone(),
        });

        let mut proof = ProofNode::new_any("Any cycle merge".into());

        // Try worst-case merge
        // TODO also good cases and then exclude the rest
        let mut cases_remain: Vec<MergeCases> = vec![];
        for m_edge in vec![data.m_last.1, data.m_last.2].into_iter().filter(
            |m_edge| matches!(m_edge.hit(), PathMatchingHits::Path(r) if r <= context.path_len - 3),
        ) {
            if check_nice_path_with_cycle(
                &case_path,
                m_edge,
                false,
                context.credit_inv.clone(),
                &mut proof,
            ) {
                return proof;
            } else if check_nice_path_with_cycle(
                &case_path,
                m_edge,
                true,
                context.credit_inv.clone(),
                &mut proof,
            ) {
                cases_remain.push(MergeCases::NoNicePair(m_edge))
                // it remains to check merge for non-nice pair hit
            } else {
                cases_remain.push(MergeCases::NoNicePair(m_edge));
                cases_remain.push(MergeCases::NicePair(m_edge));
                // it remains to check merge for nice pair and non-nice pair
            }
        }

        proof.add_child(ProofNode::new_leaf("Tactics exhausted".into(), false));

        proof
    }
}

pub enum MergeCases {
    NoNicePair(PathMatchingEdge),
    NicePair(PathMatchingEdge),
}

fn check_nice_path_with_cycle<C: CreditInvariant>(
    path: &NicePath,
    m_cycle_edge: PathMatchingEdge,
    hit_and_out_np: bool,
    credit_inv: C,
    matching_node: &mut ProofNode,
) -> bool {
    // check worst-case merge
    let mut pseudo_nodes = path
        .nodes
        .split_at(m_cycle_edge.hits_path().unwrap())
        .1
        .to_vec();
    if let Some(SuperNode::Zoomed(zoomed)) = pseudo_nodes.last_mut() {
        zoomed.out_node = Some(m_cycle_edge.source())
    }
    if let Some(SuperNode::Abstract(abs)) = pseudo_nodes.first_mut() {
        abs.nice_pair = hit_and_out_np
    }
    let cycle = PseudoCycle {
        nodes: pseudo_nodes,
    };
    if cycle.value(credit_inv.clone()) >= Credit::from_integer(2) {
        matching_node.add_child(ProofNode::new_leaf(
            format!("PseudoCycle {} merged!", cycle),
            true,
        ));
        return true;
    } else {
        matching_node.add_child(ProofNode::new_leaf(
            format!("Failed worst-case merge for PseudoCycle {} ", cycle),
            false,
        ));
        return false;
    }
}
