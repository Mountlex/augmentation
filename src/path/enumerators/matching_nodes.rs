use itertools::Itertools;

use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    AugmentedPathInstance, SelectedHitInstance,
};

#[derive(Clone)]
pub struct MatchingNodesEnum;

pub struct MatchingNodesEnumerator<'a> {
    pub instance: &'a AugmentedPathInstance,
    pub hit_comp_idx: usize,
    pub last_hit: bool,
}

impl<'a> MatchingNodesEnumerator<'a> {
    pub fn new(instance: &'a AugmentedPathInstance, hit_comp_idx: usize, last_hit: bool) -> Self {
        Self {
            instance,
            hit_comp_idx,
            last_hit
        }
    }
}

impl EnumeratorTactic<SelectedHitInstance, SelectedHitInstance> for MatchingNodesEnum {
    type Enumer<'a> = MatchingNodesEnumerator<'a>;
    fn msg(&self, data_in: &SelectedHitInstance) -> String {
        format!(
            "Enumerate matching endpoints at Path[{}]",
            data_in.hit_comp_idx
        )
    }

    fn item_msg(&self, item: &SelectedHitInstance) -> String {
        format!(
            "Selected matching between path[{}] and last component: {}",
            item.hit_comp_idx,
            item.instance
                .fixed_edges_between(item.hit_comp_idx, item.instance.path.nodes.len() - 1)
                .into_iter()
                .join(", ")
        )
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        MatchingNodesEnumerator {
            instance: &data.instance,
            hit_comp_idx: data.hit_comp_idx,
            last_hit: data.last_hit,
        }
    }
}

impl<'a> Enumerator<SelectedHitInstance> for MatchingNodesEnumerator<'a> {
    fn iter(
        &self,
        context: &crate::path::proof::ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedHitInstance> + '_> {
        let hit_comp_idx = self.hit_comp_idx;
        let last_hit = self.last_hit;
        let iter = Enumerator::<AugmentedPathInstance>::iter(self, context).map(move |aug| {
            SelectedHitInstance {
                instance: aug,
                hit_comp_idx,
                last_hit
            }
        });

        Box::new(iter)
    }
}

pub fn matching_nodes_iter(
    instance: AugmentedPathInstance,
    hit_comp_idx: usize,
    path_len: usize,
) -> Box<dyn Iterator<Item = AugmentedPathInstance>> {
    let left_comp = instance.path[hit_comp_idx].get_comp().clone();
    let hit_comp_idx = hit_comp_idx;

    if hit_comp_idx == path_len - 2 {
        let matching_edges = instance.matching_edges_hit(hit_comp_idx);

        let iter = left_comp
            .matching_permutations(matching_edges.len())
            .into_iter()
            .filter(move |left_matched| {
                left_matched
                    .iter()
                    .all(|matched| *matched != left_comp.fixed_node())
            })
            .map(move |left_matched| {
                let mut instance = instance.clone();
                for (left, right) in left_matched.into_iter().zip(matching_edges.iter()) {
                    instance.fix_matching_edge(right.source(), hit_comp_idx, left);
                }
                instance
            });

        return Box::new(iter);
    } else {
        let matching_edges = instance.matching_edges_hit(hit_comp_idx);

        let iter = left_comp
            .matching_permutations(matching_edges.len())
            .into_iter()
            .map(move |left_matched| {
                let mut instance = instance.clone();
                for (left, right) in left_matched.into_iter().zip(matching_edges.iter()) {
                    instance.fix_matching_edge(right.source(), hit_comp_idx, left);
                }
                instance
            });

        return Box::new(iter);
    }
}

impl<'a> Enumerator<AugmentedPathInstance> for MatchingNodesEnumerator<'a> {
    fn iter(&self, context: &ProofContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        matching_nodes_iter(self.instance.clone(), self.hit_comp_idx, context.path_len)
    }
}
