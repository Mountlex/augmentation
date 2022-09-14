use itertools::Itertools;

use crate::{
    comps::{Component, Node},
    path::{
        proof::{Enumerator, EnumeratorTactic, ProofContext},
        Matching3, NicePairConfig, SelectedHitInstance, SelectedMatchingInstance,
    },
    types::Edge,
};

pub struct MatchingNodesEnumTactic;

pub struct MatchingNodesEnumerator<'a> {
    instance: &'a SelectedHitInstance,
}

impl EnumeratorTactic<SelectedHitInstance, SelectedMatchingInstance> for MatchingNodesEnumTactic {
    type Enumer<'a> = MatchingNodesEnumerator<'a>;
    fn msg(&self, data_in: &SelectedHitInstance) -> String {
        format!(
            "Enumerate matching endpoints at Path[{}]",
            data_in.hit_comp_idx
        )
    }

    fn item_msg(&self, item: &SelectedMatchingInstance) -> String {
        format!(
            "Selected Matching {:?} between path[{}] and last component",
            item.matched, item.hit_comp_idx
        )
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        MatchingNodesEnumerator { instance: data }
    }
}

impl<'a> Enumerator<SelectedHitInstance, SelectedMatchingInstance> for MatchingNodesEnumerator<'a> {
    fn iter(
        &mut self,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedMatchingInstance> + '_> {
        let left_comp =
            self.instance.path_matching.path.nodes[self.instance.hit_comp_idx].get_comp();

        let iter = left_comp
            .matching_permutations(self.instance.matched.len())
            .into_iter()
            .map(move |left_matched| SelectedMatchingInstance {
                matched: self
                    .instance
                    .matched
                    .iter()
                    .zip(left_matched.into_iter())
                    .map(|(r, l)| Edge(l, r.source()))
                    .collect_vec(),
                hit_comp_idx: self.instance.hit_comp_idx,
                path_matching: self.instance.path_matching.clone(),
            });

        Box::new(iter)
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
