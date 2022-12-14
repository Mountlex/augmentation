use crate::{
    path::{proof::PathContext, AbstractEdge, AugmentedPathInstance, PathHit, Pidx},
    proof_logic::{Enumerator, EnumeratorTactic},
};

#[derive(Clone)]
pub struct MatchingHitEnum;

pub struct MatchingHitEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance, PathContext> for MatchingHitEnumerator<'a> {
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let path_len = self.instance.path_len();
        let comp = self.instance[Pidx::Last].get_comp();

        let mut targets = vec![PathHit::Outside];
        for i in 1..path_len {
            targets.push(PathHit::Path(i.into()));
        }

        let instance = self.instance.clone();

        let iter = self
            .instance
            .unmatched_nodes(Pidx::Last)
            .into_iter()
            .filter(|n| {
                comp.is_large() || *n != self.instance[Pidx::Last].get_zoomed().in_node.unwrap()
            })
            .flat_map(move |source| {
                let instance_clone = instance.clone();
                targets.clone().into_iter().map(move |hit| {
                    let mut instance_clone = instance_clone.clone();
                    instance_clone
                        .abstract_edges
                        .push(AbstractEdge::new(Pidx::Last, source, hit));
                    instance_clone
                })
            });

        Box::new(iter)
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext>
    for MatchingHitEnum
{
    type Enumer<'a> = MatchingHitEnumerator<'a>;

    fn msg(&self, _data_in: &AugmentedPathInstance) -> String {
        format!("Enumerate all matching hits from last component")
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("{:?}", item.abstract_edges)
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        MatchingHitEnumerator { instance: data }
    }
}
