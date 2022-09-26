use itertools::Itertools;

use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    AugmentedPathInstance, MatchingEdge, PathHit,
};

#[derive(Clone)]
pub struct MatchingHitEnum {
    comp_index: usize,
}

pub struct MatchingHitEnumerator<'a> {
    comp_index: usize,
    instance: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance> for MatchingHitEnumerator<'a> {
    fn iter(&self, context: &ProofContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        assert!(self.comp_index > 0);

        let path_len = context.path_len;
        let comp = self.instance.path[self.comp_index].get_comp();
        let nodes = comp.graph().nodes().collect_vec();

        let mut targets = vec![PathHit::Outside];
        for i in 0..path_len {
            if i != self.comp_index {
                targets.push(PathHit::Path(i));
            }
        }

        let num_edges = if self.comp_index == context.path_len - 1 {
            2
        } else {
            1
        };

        let instance = self.instance.clone();

        let iter = nodes
            .into_iter()
            .filter(|n| *n != comp.fixed_node()) // in of last component already matched!
            .permutations(num_edges)
            .flat_map(move |m_endpoints| {
                let instance_clone = instance.clone();
                targets
                    .clone()
                    .into_iter()
                    .combinations_with_replacement(num_edges)
                    .map(move |hits| {
                        let mut matching_edges = m_endpoints
                            .iter()
                            .zip(hits.into_iter())
                            .map(|(source, hit)| MatchingEdge::new(path_len - 1, *source, hit))
                            .collect_vec();

                        let mut instance_clone = instance_clone.clone();
                        instance_clone
                            .non_path_matching_edges
                            .append(&mut matching_edges);
                        instance_clone
                    })
            });

        Box::new(iter)
    }
}

impl MatchingHitEnum {
    pub fn for_comp(idx: usize) -> Self {
        Self { comp_index: idx }
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance> for MatchingHitEnum {
    type Enumer<'a> = MatchingHitEnumerator<'a>;

    fn msg(&self, _data_in: &AugmentedPathInstance) -> String {
        format!("Enumerate all matching hits from last component")
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("{:?}", item.non_path_matching_edges)
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        MatchingHitEnumerator {
            comp_index: self.comp_index,
            instance: data,
        }
    }
}
