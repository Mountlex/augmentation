use itertools::Itertools;

use crate::{
    comps::Node,
    path::{proof::Enumerator, NicePairConfig, NicePath, PathMatchingHits, ThreeMatching},
};

#[derive(Clone)]
pub struct ComponentHitInput {
    pub nice_path: NicePath,
    pub three_matching: ThreeMatching,
    pub npc_last: NicePairConfig,
}

pub struct ComponentHitEnumerator;

impl Enumerator for ComponentHitEnumerator {
    type In = ComponentHitInput;

    type Out = ComponentHitOutput;

    fn msg(&self, data_in: &Self::In) -> String {
        format!("Enumerate all components hit by matching edges")
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let mut matching = data_in.three_matching.to_vec();
        matching.sort_by_key(|m| m.hit());

        let iter = matching
            .clone()
            .into_iter()
            .filter(|m_edge| m_edge.hits_path().is_some())
            .map(|m_edge| m_edge.hit())
            .dedup_with_count()
            .flat_map(move |(num_edges, hit_comp)| {
                if let PathMatchingHits::Path(hit_comp_idx) = hit_comp {
                    let right_matched: Vec<Node> = matching
                        .iter()
                        .filter(|m_edge| m_edge.hit() == hit_comp)
                        .map(|m_edge| m_edge.source())
                        .collect();
                    assert_eq!(right_matched.len(), num_edges);

                    Some(ComponentHitOutput {
                        path: data_in.nice_path.clone(),
                        npc_last: data_in.npc_last.clone(),
                        three_matching: data_in.three_matching.clone(),
                        hit_comp_idx,
                        right_matched,
                    })
                } else {
                    None
                }
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!(
            "Path[{}] hit by {} matching edges",
            item.hit_comp_idx,
            item.right_matched.len()
        )
    }
}

#[derive(Clone)]
pub struct ComponentHitOutput {
    pub path: NicePath,
    pub npc_last: NicePairConfig,
    pub three_matching: ThreeMatching,
    pub hit_comp_idx: usize,
    pub right_matched: Vec<Node>,
}
