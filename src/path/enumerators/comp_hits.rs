use itertools::Itertools;

use crate::{
    path::{proof::PathContext, AugmentedPathInstance, PathHit, SelectedHitInstance},
    proof_logic::{Enumerator, EnumeratorTactic},
};

#[derive(Clone)]
pub struct ComponentHitEnum;

pub struct ComponentHitEnumerator<'a> {
    input: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<SelectedHitInstance, PathContext> for ComponentHitEnumerator<'a> {
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = SelectedHitInstance> + '_> {
        let mut matching_edges = self.input.non_path_matching_edges.clone();
        matching_edges.sort_by_key(|m| m.hit());
        let mut num_path_matching_edges =
            matching_edges.len() - self.input.all_outside_hits().len();
        let iter = matching_edges
            .clone()
            .into_iter()
            .filter(|m_edge| m_edge.hits_path().is_some())
            .map(|m_edge| m_edge.hit())
            .dedup_with_count()
            .flat_map(move |(num_edges, hit_comp)| {
                num_path_matching_edges -= num_edges;
                if let PathHit::Path(hit_comp_idx) = hit_comp {
                    Some(SelectedHitInstance {
                        instance: self.input.clone(),
                        hit_comp_idx,
                        last_hit: num_path_matching_edges == 0,
                    })
                } else {
                    None
                }
            });

        Box::new(iter)
    }
}

impl EnumeratorTactic<AugmentedPathInstance, SelectedHitInstance, PathContext>
    for ComponentHitEnum
{
    type Enumer<'a> = ComponentHitEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &AugmentedPathInstance) -> String {
        format!("Enumerate all components hit by matching edges")
    }

    fn item_msg(&self, item: &SelectedHitInstance) -> String {
        format!("Path[{}] hit by matching edges", item.hit_comp_idx,)
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        ComponentHitEnumerator { input: data }
    }
}
