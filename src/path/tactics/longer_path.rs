use crate::{
    comps::Component,
    path::{
        enumerators::{matching_hits::MatchingHitEnumeratorOutput, nice_pairs::NPCEnumOutput},
        proof::{or, ProofContext, Tactic},
        NicePairConfig, NicePath, PathMatchingEdge, ThreeMatching,
    },
    proof_tree::ProofNode,
};

impl From<NPCEnumOutput<MatchingHitEnumeratorOutput>> for LongerPathInput {
    fn from(o: NPCEnumOutput<MatchingHitEnumeratorOutput>) -> Self {
        LongerPathInput {
            nice_path: o.input.nice_path,
            three_matching: o.input.three_matching,
            npc: o.npc,
        }
    }
}

pub struct LongerPathInput {
    nice_path: NicePath,
    three_matching: ThreeMatching,
    npc: NicePairConfig,
}

pub struct LongerPathTactic;

impl Tactic for LongerPathTactic {
    type In = LongerPathInput;

    fn action(&self, data: Self::In, context: &ProofContext) -> crate::proof_tree::ProofNode {
        let check_input = LongerNicePathCheckInput {
            last_comp_ref: data.nice_path.nodes.last().unwrap().get_comp(),
            np_config: &data.npc,
            last_pseudo_edge: &data.three_matching.0,
        };

        if data.three_matching.1.hits_outside() && data.three_matching.2.hits_outside() {
            or(
                LongerNicePathCheck::check_for(&data.three_matching.1),
                LongerNicePathCheck::check_for(&data.three_matching.2),
            )
            .action(check_input, context)
        } else if data.three_matching.1.hits_outside() {
            LongerNicePathCheck::check_for(&data.three_matching.1).action(check_input, context)
        } else if data.three_matching.2.hits_outside() {
            LongerNicePathCheck::check_for(&data.three_matching.2).action(check_input, context)
        } else {
            ProofNode::new_leaf(format!("None of the matching edges hits outside"), false)
        }
    }
}

// Private tactics (subroutines)

#[derive(Clone)]
struct LongerNicePathCheckInput<'a> {
    last_comp_ref: &'a Component,
    np_config: &'a NicePairConfig,
    last_pseudo_edge: &'a PathMatchingEdge,
}

struct LongerNicePathCheck<'a> {
    other_matching_edge: &'a PathMatchingEdge,
}

impl<'a> LongerNicePathCheck<'a> {
    fn check_for(other_matching_edge: &'a PathMatchingEdge) -> Self {
        LongerNicePathCheck {
            other_matching_edge,
        }
    }
}

impl<'a> Tactic for LongerNicePathCheck<'a> {
    type In = LongerNicePathCheckInput<'a>;

    fn action(&self, data: Self::In, context: &ProofContext) -> crate::proof_tree::ProofNode {
        if data.last_comp_ref.is_c6()
            || data.last_comp_ref.is_large()
            || data.np_config.is_nice_pair(
                data.last_pseudo_edge.source(),
                self.other_matching_edge.source(),
            )
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
