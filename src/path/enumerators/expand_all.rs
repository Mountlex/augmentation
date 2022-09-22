use itertools::Itertools;

use crate::path::{
    proof::{Enumerator, EnumeratorTactic},
    AugmentedPathInstance, SelectedHitInstance,
};

use super::{expand::ExpandEnumerator, matching_nodes::MatchingNodesEnumerator};

pub struct ExpandAllEnum;

pub struct ExpandAllEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance> for ExpandAllEnumerator<'a> {
    fn iter(
        &mut self,
        context: &mut crate::path::proof::ProofContext,
    ) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let mut cases = vec![self.instance.clone()];

        for (i, node) in self.instance.path.nodes.iter().enumerate() {
            if !node.is_zoomed() {
                cases = cases
                    .into_iter()
                    .flat_map(|instance| {
                        MatchingNodesEnumerator::new(&instance, i)
                            .iter(context)
                            .flat_map(|instance| {
                                Enumerator::<AugmentedPathInstance>::iter(
                                    &mut ExpandEnumerator::new(&instance, i),
                                    context,
                                )
                                .collect_vec()
                            })
                            .collect_vec()
                    })
                    .collect_vec()
            }
        }

        assert!(cases.iter().all(|case| case.path.nodes.iter().all(|node| node.is_zoomed())));
        assert!(cases.iter().all(|case| case.non_path_matching_edges.is_empty()));

        Box::new(cases.into_iter())
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance> for ExpandAllEnum {
    type Enumer<'a> = ExpandAllEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        format!("Expand remaining nodes")
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        ExpandAllEnumerator { instance: data }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Expanded nice path {}", item.path)
    }
}

impl EnumeratorTactic<SelectedHitInstance, AugmentedPathInstance> for ExpandAllEnum {
    type Enumer<'a> = ExpandAllEnumerator<'a>;

    fn msg(&self, _data: &SelectedHitInstance) -> String {
        format!("Expand remaining nodes")
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        ExpandAllEnumerator { instance: &data.instance }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Expanded nice path {}", item.path)
    }
}
