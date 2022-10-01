use crate::{
    path::{
        enumerators::{expand::expand_iter, matching_nodes::matching_nodes_iter},
        proof::PathContext,
        AugmentedPathInstance, SelectedHitInstance,
    },
    proof_logic::{Enumerator, EnumeratorTactic},
};

#[derive(Clone)]
pub struct ExpandAllEnum;

pub struct ExpandAllEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance, PathContext> for ExpandAllEnumerator<'a> {
    fn iter(
        &self,
        context: &crate::path::proof::PathContext,
    ) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let mut cases: Box<dyn Iterator<Item = AugmentedPathInstance>> =
            Box::new(vec![self.instance.clone()].into_iter());
        let path_len = context.path_len;

        for (i, _node) in self.instance.path.nodes.iter().enumerate() {
            //if !node.is_zoomed() {
            let context = context.clone();
            cases = Box::new(cases.into_iter().flat_map(move |instance| {
                let i = i;
                let context = context.clone();
                matching_nodes_iter(instance, i, path_len)
                    .flat_map(move |instance| expand_iter(instance, i, context.clone()))
            }));
            //}
        }

        //let vec_cases = cases.collect_vec();

        // assert!(vec_cases.iter()
        //     .all(|case| case.path.nodes.iter().all(|node| node.is_zoomed())));
        // assert!(vec_cases.iter()
        //     .all(|case| case.non_path_matching_edges.len() == case.outside_hits().len()));

        //Box::new(vec_cases.into_iter())
        cases
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext> for ExpandAllEnum {
    type Enumer<'a> = ExpandAllEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        format!("Expand remaining nodes")
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        ExpandAllEnumerator { instance: data }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Nice path {}", item.path)
    }
}

impl EnumeratorTactic<SelectedHitInstance, AugmentedPathInstance, PathContext> for ExpandAllEnum {
    type Enumer<'a> = ExpandAllEnumerator<'a>;

    fn msg(&self, _data: &SelectedHitInstance) -> String {
        format!("Expand remaining nodes")
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        ExpandAllEnumerator {
            instance: &data.instance,
        }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Nice path {}", item.path)
    }
}
