use crate::{
    comps::{Component, Node},
    path::{proof::Enumerator, NicePairConfig, ThreeMatching},
};

use super::comp_hits::ComponentHitOutput;

impl From<ComponentHitOutput> for MatchingNodesEnumeratorInput {
    fn from(o: ComponentHitOutput) -> Self {
        MatchingNodesEnumeratorInput {
            three_matching: o.three_matching,
            right_matched: o.right_matched,
            last_comp: o.path.nodes.last().unwrap().get_comp().clone(),
            left_comp: o.path.nodes[o.hit_comp_idx].get_comp().clone(),
            npc_last: o.npc_last,
        }
    }
}

#[derive(Clone)]
pub struct MatchingNodesEnumeratorInput {
    pub right_matched: Vec<Node>,
    pub three_matching: ThreeMatching,
    pub last_comp: Component,
    pub left_comp: Component,
    pub npc_last: NicePairConfig,
}

pub struct MatchingNodesEnumerator;

impl Enumerator for MatchingNodesEnumerator {
    type In = MatchingNodesEnumeratorInput;

    type Out = MatchingNodesEnumeratorOutput;

    fn msg(&self, data_in: &Self::In) -> String {
        format!("Enumerate matching endpoints at {}", data_in.left_comp)
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let iter = data_in
            .left_comp
            .matching_permutations(data_in.right_matched.len())
            .into_iter()
            .map(move |left_matched| MatchingNodesEnumeratorOutput {
                three_matching: data_in.three_matching.clone(),
                left_matched,
                right_matched: data_in.right_matched.clone(),
                last_comp: data_in.last_comp.clone(),
                left_comp: data_in.left_comp.clone(),
                npc_last: data_in.npc_last.clone(),
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!("Matching endpoints {:?}", item.left_matched)
    }
}

#[derive(Clone)]
pub struct MatchingNodesEnumeratorOutput {
    pub three_matching: ThreeMatching,
    pub left_matched: Vec<Node>,
    pub right_matched: Vec<Node>,
    pub last_comp: Component,
    pub left_comp: Component,
    pub npc_last: NicePairConfig,
}
