use itertools::Itertools;

use crate::{
    comps::{Component, Node},
    path::{
        proof::{Enumerator, ProofContext},
        Matching3, NicePairConfig, SelectedHitInstance, SelectedMatchingInstance,
    },
    types::Edge,
};

pub struct MatchingNodesEnumerator;

impl Enumerator<SelectedHitInstance, SelectedMatchingInstance> for MatchingNodesEnumerator {
    fn msg(&self, data_in: &SelectedHitInstance) -> String {
        format!(
            "Enumerate matching endpoints at Path[{}]",
            data_in.hit_comp_idx
        )
    }

    fn iter(
        &self,
        instance: SelectedHitInstance,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedMatchingInstance>> {
        let left_comp = instance.path_matching.path.nodes[instance.hit_comp_idx].get_comp();

        let iter = left_comp
            .matching_permutations(instance.matched.len())
            .into_iter()
            .map(move |left_matched| SelectedMatchingInstance {
                matched: instance
                    .matched
                    .iter()
                    .zip(left_matched.into_iter())
                    .map(|(r, l)| Edge(l, r.source()))
                    .collect_vec(),
                hit_comp_idx: instance.hit_comp_idx,
                path_matching: instance.path_matching.clone(),
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &SelectedMatchingInstance) -> String {
        format!("Selected Matching {:?} between path[{}] and last component", item.matched, item.hit_comp_idx)
    }
}

#[derive(Clone)]
pub struct MatchingNodesEnumeratorOutput {
    pub three_matching: Matching3,
    pub left_matched: Vec<Node>,
    pub right_matched: Vec<Node>,
    pub last_comp: Component,
    pub left_comp: Component,
    pub npc_last: NicePairConfig,
}
