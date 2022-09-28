use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    AugmentedPathInstance, MatchingEdge, PathHit,
};

#[derive(Clone)]
pub struct MatchingHitEnum;

pub struct MatchingHitEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance> for MatchingHitEnumerator<'a> {
    fn iter(&self, context: &ProofContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let path_len = context.path_len;
        let comp = self.instance.path.last_comp();

        let mut targets = vec![PathHit::Outside];
        for i in 0..path_len - 1 {
            targets.push(PathHit::Path(i));
        }

        let instance = self.instance.clone();

        let iter = self
            .instance
            .unmatched_nodes(path_len - 1)
            .into_iter()
            .filter(|n| comp.is_large() || n != &comp.fixed_node())
            .flat_map(move |source| {
                let instance_clone = instance.clone();
                targets.clone().into_iter().map(move |hit| {
                    let mut instance_clone = instance_clone.clone();
                    instance_clone
                        .non_path_matching_edges
                        .push(MatchingEdge::new(path_len - 1, source, hit));
                    instance_clone
                })
            });

        Box::new(iter)
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
        MatchingHitEnumerator { instance: data }
    }
}
