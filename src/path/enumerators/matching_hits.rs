use itertools::Itertools;

use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    Matching3, MatchingEdge, PathHit, PathInstance, PathMatchingInstance,
};

pub struct MatchingHitEnumTactic {
    comp_index: usize,
}

pub struct MatchingHitEnumerator<'a> {
    comp_index: usize,
    path: &'a PathInstance,
}

impl<'a> Enumerator<PathInstance, PathMatchingInstance> for MatchingHitEnumerator<'a> {
    fn iter(
        &mut self,
        context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = PathMatchingInstance> + '_> {
        assert!(self.comp_index > 0);

        let path_len = self.path.nodes.len();
        let comp = self.path.nodes[self.comp_index].get_comp();
        let nodes = comp.graph().nodes().collect_vec();

        let mut targets = vec![PathHit::Outside];
        for i in 0..path_len {
            if i != self.comp_index {
                targets.push(PathHit::Path(i));
            }
        }

        let free_edges = if self.comp_index == context.path_len - 1 {
            2
        } else {
            1
        };

        let path = self.path.clone();
        let comp_index = self.comp_index;

        let iter = nodes
            .into_iter()
            .permutations(3)
            .flat_map(move |m_endpoints| {
                let path_clone = path.clone();
                targets
                    .clone()
                    .into_iter()
                    .combinations_with_replacement(free_edges)
                    .map(move |hits| {
                        let matching = if free_edges == 2 {
                            let m1 = MatchingEdge(m_endpoints[1], hits[0]);
                            let m2 = MatchingEdge(m_endpoints[2], hits[1]);
                            Matching3 {
                                source_comp_idx: comp_index,
                                path_edge_left: MatchingEdge(
                                    m_endpoints[0],
                                    PathHit::Path(path_len - 2),
                                )
                                .into(),
                                path_edge_right: None,
                                other_edges: vec![m1, m2],
                            }
                        } else {
                            let m2 = MatchingEdge(m_endpoints[2], hits[0]);
                            Matching3 {
                                source_comp_idx: comp_index,
                                path_edge_left: MatchingEdge(
                                    m_endpoints[0],
                                    PathHit::Path(comp_index - 1),
                                )
                                .into(),
                                path_edge_right: MatchingEdge(
                                    m_endpoints[1],
                                    PathHit::Path(comp_index + 1),
                                )
                                .into(),
                                other_edges: vec![m2],
                            }
                        };

                        PathMatchingInstance {
                            path: path_clone.clone(),
                            matching,
                        }
                    })
            });

        Box::new(iter)
    }
}

impl MatchingHitEnumTactic {
    pub fn for_comp(idx: usize) -> Self {
        Self { comp_index: idx }
    }
}

impl EnumeratorTactic<PathInstance, PathMatchingInstance> for MatchingHitEnumTactic {
    type Enumer<'a> = MatchingHitEnumerator<'a>;

    fn msg(&self, _data_in: &PathInstance) -> String {
        format!("Enumerate all matching hits from last component")
    }

    fn item_msg(&self, item: &PathMatchingInstance) -> String {
        format!("{}", item.matching)
    }

    fn get_enumerator<'a>(&'a self, data: &'a PathInstance) -> Self::Enumer<'a> {
        MatchingHitEnumerator {
            comp_index: self.comp_index,
            path: data,
        }
    }
}
