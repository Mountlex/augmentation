use itertools::Itertools;

use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    Matching3, MatchingEdge, NicePairConfig, PathHit, PathInstance, PathMatchingInstance,
    SelectedHitInstance,
};

pub struct ComponentHitEnumTactic;

pub struct ComponentHitEnumerator<'a> {
    input: &'a PathMatchingInstance,
}

impl<'a> Enumerator<PathMatchingInstance, SelectedHitInstance> for ComponentHitEnumerator<'a> {
    fn iter(
        &mut self,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedHitInstance> + '_> {
        let mut matching = self.input.matching.to_vec();
        matching.sort_by_key(|m| m.hit());

        let iter = matching
            .clone()
            .into_iter()
            .filter(|m_edge| m_edge.hits_path().is_some())
            .map(|m_edge| m_edge.hit())
            .dedup_with_count()
            .flat_map(move |(num_edges, hit_comp)| {
                if let PathHit::Path(hit_comp_idx) = hit_comp {
                    let matched: Vec<MatchingEdge> = matching
                        .iter()
                        .filter(|m_edge| m_edge.hit() == hit_comp)
                        .cloned()
                        .collect();
                    assert_eq!(matched.len(), num_edges);

                    Some(SelectedHitInstance {
                        path_matching: self.input.clone(),
                        hit_comp_idx,
                        matched,
                    })
                } else {
                    None
                }
            });

        Box::new(iter)
    }
}

impl EnumeratorTactic<PathMatchingInstance, SelectedHitInstance> for ComponentHitEnumTactic {
    type Enumer<'a> = ComponentHitEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &PathMatchingInstance) -> String {
        format!("Enumerate all components hit by matching edges")
    }

    fn item_msg(&self, item: &SelectedHitInstance) -> String {
        format!(
            "Path[{}] hit by {} matching edges",
            item.hit_comp_idx,
            item.matched.len()
        )
    }

    fn get_enumerator<'a>(&'a self, data: &'a PathMatchingInstance) -> Self::Enumer<'a> {
        ComponentHitEnumerator { input: data }
    }
}
