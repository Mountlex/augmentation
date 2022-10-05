use itertools::Itertools;

use crate::{
    path::{proof::PathContext, AugmentedPathInstance, Pidx, SelectedHitInstance},
    proof_logic::{Enumerator, EnumeratorTactic},
};

#[derive(Clone)]
pub struct MatchingNodesEnum;

pub struct MatchingNodesEnumerator<'a> {
    pub instance: &'a AugmentedPathInstance,
    pub hit_comp_idx: Pidx,
    pub last_hit: bool,
}

impl<'a> MatchingNodesEnumerator<'a> {
    pub fn _new(instance: &'a AugmentedPathInstance, hit_comp_idx: Pidx, last_hit: bool) -> Self {
        Self {
            instance,
            hit_comp_idx,
            last_hit,
        }
    }
}

impl EnumeratorTactic<SelectedHitInstance, SelectedHitInstance, PathContext> for MatchingNodesEnum {
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
                .fixed_edges_between(item.hit_comp_idx, Pidx::Last)
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

impl<'a> Enumerator<SelectedHitInstance, PathContext> for MatchingNodesEnumerator<'a> {
    fn iter(
        &self,
        context: &crate::path::proof::PathContext,
    ) -> Box<dyn Iterator<Item = SelectedHitInstance> + '_> {
        let hit_comp_idx = self.hit_comp_idx;
        let last_hit = self.last_hit;
        let iter =
            Enumerator::<AugmentedPathInstance, PathContext>::iter(self, context).map(move |aug| {
                SelectedHitInstance {
                    instance: aug,
                    hit_comp_idx,
                    last_hit,
                }
            });

        Box::new(iter)
    }
}

pub fn matching_nodes_iter(
    instance: AugmentedPathInstance,
    hit_comp_idx: Pidx,
) -> Box<dyn Iterator<Item = AugmentedPathInstance>> {
    let hit_comp_idx = hit_comp_idx;
    let hit_comp = instance[hit_comp_idx].get_comp().clone();

    if hit_comp_idx.is_prelast() {
        let matching_edges = instance.matching_edges_hit(hit_comp_idx);

        let iter = hit_comp
            .matching_permutations(matching_edges.len())
            .into_iter()
            .filter(move |left_matched| {
                left_matched
                    .iter()
                    .all(|matched| *matched != hit_comp.fixed_node())
            })
            .map(move |left_matched| {
                let mut instance = instance.clone();
                for (left, right) in left_matched.into_iter().zip(matching_edges.iter()) {
                    instance.fix_matching_edge(&right, hit_comp_idx, left);
                }
                instance
            });

        return Box::new(iter);
    } else {
        let matching_edges = instance.matching_edges_hit(hit_comp_idx);

        let iter = hit_comp
            .matching_permutations(matching_edges.len())
            .into_iter()
            .map(move |left_matched| {
                let mut instance = instance.clone();
                for (left, right) in left_matched.into_iter().zip(matching_edges.iter()) {
                    instance.fix_matching_edge(&right, hit_comp_idx, left);
                }
                instance
            });

        return Box::new(iter);
    }
}

impl<'a> Enumerator<AugmentedPathInstance, PathContext> for MatchingNodesEnumerator<'a> {
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        matching_nodes_iter(self.instance.clone(), self.hit_comp_idx)
    }
}
