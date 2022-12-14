use crate::{
    path::{
        enumerators::{expand::expand_iter, matching_nodes::matching_nodes_iter},
        proof::PathContext,
        AugmentedPathInstance, Pidx, SelectedHitInstance,
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

        for (i, _node) in self.instance.nodes.iter().enumerate() {
            let context = context.clone();
            cases = Box::new(cases.into_iter().flat_map(move |instance| {
                let context = context.clone();
                matching_nodes_iter(instance, i.into())
                    .flat_map(move |instance| expand_iter(instance, Pidx::from(i), context.clone()))
            }));
        }

        cases
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext> for ExpandAllEnum {
    type Enumer<'a> = ExpandAllEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        String::new()
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        ExpandAllEnumerator { instance: data }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Nice path {}", item)
    }
}

impl EnumeratorTactic<SelectedHitInstance, AugmentedPathInstance, PathContext> for ExpandAllEnum {
    type Enumer<'a> = ExpandAllEnumerator<'a>;

    fn msg(&self, _data: &SelectedHitInstance) -> String {
        String::new()
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        ExpandAllEnumerator {
            instance: &data.instance,
        }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Nice path {}", item)
    }
}
