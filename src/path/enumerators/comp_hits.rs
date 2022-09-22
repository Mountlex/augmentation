use itertools::Itertools;

use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    AugmentedPathInstance, PathHit, SelectedHitInstance,
};

pub struct ComponentHitEnumTactic;

pub struct ComponentHitEnumerator<'a> {
    input: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<SelectedHitInstance> for ComponentHitEnumerator<'a> {
    fn iter(
        &mut self,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedHitInstance> + '_> {
        let mut matching_edges = self.input.non_path_matching_edges.clone();
        matching_edges.sort_by_key(|m| m.hit());
        let iter = matching_edges
            .clone()
            .into_iter()
            .filter(|m_edge| m_edge.hits_path().is_some())
            .map(|m_edge| m_edge.hit())
            .dedup_with_count()
            .flat_map(move |(_num_edges, hit_comp)| {
                if let PathHit::Path(hit_comp_idx) = hit_comp {
                    Some(SelectedHitInstance {
                        instance: self.input.clone(),
                        hit_comp_idx,
                    })
                } else {
                    None
                }
            });

        Box::new(iter)
    }
}

impl EnumeratorTactic<AugmentedPathInstance, SelectedHitInstance> for ComponentHitEnumTactic {
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
