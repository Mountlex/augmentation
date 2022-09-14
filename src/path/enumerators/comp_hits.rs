use itertools::Itertools;

use crate::path::{
    proof::{Enumerator, ProofContext},
    Matching3, MatchingEdge, NicePairConfig, PathHit, PathInstance, PathMatchingInstance,
    SelectedHitInstance,
};

#[derive(Clone)]
pub struct ComponentHitInput {
    pub nice_path: PathInstance,
    pub three_matching: Matching3,
    pub npc_last: NicePairConfig,
}

pub struct ComponentHitEnumerator;

impl Enumerator<PathMatchingInstance, SelectedHitInstance> for ComponentHitEnumerator {
    fn msg(&self, _data_in: &PathMatchingInstance) -> String {
        format!("Enumerate all components hit by matching edges")
    }

    fn iter(
        &mut self,
        instance: PathMatchingInstance,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedHitInstance>> {
        let mut matching = instance.matching.to_vec();
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
                        path_matching: instance.clone(),
                        hit_comp_idx,
                        matched,
                    })
                } else {
                    None
                }
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &SelectedHitInstance) -> String {
        format!(
            "Path[{}] hit by {} matching edges",
            item.hit_comp_idx,
            item.matched.len()
        )
    }
}
