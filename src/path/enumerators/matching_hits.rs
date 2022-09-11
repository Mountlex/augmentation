use itertools::Itertools;

use crate::path::{proof::Enumerator, NicePath, PathMatchingEdge, PathMatchingHits, ThreeMatching};

use super::nice_paths::PathEnumeratorOutput;

impl From<PathEnumeratorOutput> for MatchingHitEnumeratorInput {
    fn from(o: PathEnumeratorOutput) -> Self {
        MatchingHitEnumeratorInput {
            nice_path: o.nice_path,
        }
    }
}

pub struct MatchingHitEnumeratorInput {
    nice_path: NicePath,
}

pub struct MatchingHitEnumerator;

#[derive(Clone)]
pub struct MatchingHitEnumeratorOutput {
    pub nice_path: NicePath,
    pub three_matching: ThreeMatching,
}

impl Enumerator for MatchingHitEnumerator {
    type In = MatchingHitEnumeratorInput;

    type Out = MatchingHitEnumeratorOutput;

    fn msg(&self, _data_in: &Self::In) -> String {
        format!("Enumerate all matching hits from last component")
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let path_len = data_in.nice_path.nodes.len();
        let last_comp = data_in.nice_path.nodes.last().unwrap().get_comp();
        let nodes = last_comp.graph().nodes().collect_vec();

        let mut targets = vec![PathMatchingHits::Outside];
        for i in 0..path_len - 1 {
            targets.push(PathMatchingHits::Path(i));
        }

        let path = data_in.nice_path.clone();

        let iter = nodes
            .into_iter()
            .permutations(3)
            .flat_map(move |m_endpoints| {
                let path_clone = path.clone();
                targets
                    .clone()
                    .into_iter()
                    .combinations_with_replacement(2)
                    .map(move |hits| {
                        let m_path =
                            PathMatchingEdge(m_endpoints[0], PathMatchingHits::Path(path_len - 2));
                        let m1 = PathMatchingEdge(m_endpoints[1], hits[0]);
                        let m2 = PathMatchingEdge(m_endpoints[2], hits[1]);
                        let m = ThreeMatching(m_path, m1, m2);

                        MatchingHitEnumeratorOutput {
                            nice_path: path_clone.clone(),
                            three_matching: m,
                        }
                    })
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!(
            "Matching [({}), ({}), ({})]",
            item.three_matching.0, item.three_matching.1, item.three_matching.2
        )
    }
}
