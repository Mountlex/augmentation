use itertools::Itertools;

use crate::{
    path::{
        enumerators::expand::expand_iter, proof::PathContext, AugmentedPathInstance, Pidx,
        SelectedHitInstance, SuperNode, AbstractEdge,
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

        for (i, _node) in self.instance.nodes.iter().enumerate().take(self.instance.path_len() - 1) {

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

fn matching_nodes_iter(
    instance: AugmentedPathInstance,
    source_comp_idx: Pidx,
) -> Box<dyn Iterator<Item = AugmentedPathInstance>> {
    let source_comp_idx = source_comp_idx;
    let source_matching_edges = instance
        .abstract_edges
        .clone()
        .into_iter()
        .filter(|e| e.source_path == source_comp_idx)
        .collect_vec();

    let mut iter: Box<dyn Iterator<Item = AugmentedPathInstance>> =
        Box::new(vec![instance.clone()].into_iter());
    for (i, n) in instance.nodes.clone().into_iter().enumerate() {
        let idx = Pidx::from(i);
        if let SuperNode::RemPath(_) = instance[idx] {
            continue;
        } 
        let hit_comp = n.get_comp().clone();

        // all matching edges between source_comp_idx and idx
        let matching_edges = source_matching_edges
            .clone()
            .into_iter()
            .filter(|e| e.hits_path() == Some(idx))
            .collect_vec();

        iter = Box::new(iter.into_iter().flat_map(move |instance| {
            let matching_edges = matching_edges.clone();
            let hit_comp = hit_comp.clone();

            let tmp: Box<dyn Iterator<Item = AugmentedPathInstance>> =
                if let SuperNode::RemPath(_) = instance[idx] {
                    Box::new(std::iter::once(instance))
                } else if idx.prec() == source_comp_idx {
                    let iter = hit_comp
                        .matching_permutations(matching_edges.len())
                        .into_iter()
                        .filter(move |prelast_matched| {
                            if let Some(future_out) = hit_comp.fixed_node() {
                                prelast_matched.iter().all(|matched| *matched != future_out)
                            } else {
                                true
                            }
                        })
                        .map(move |prelast_matched| {
                            let mut instance = instance.clone();
                            for (prelast, matching_edge) in
                                prelast_matched.into_iter().zip(matching_edges.iter())
                            {
                                instance.fix_matching_edge(&matching_edge, idx, prelast);
                            }
                            instance
                        });

                    Box::new(iter)
                } else {
                    let matching_edges = instance.matching_edges_hit(idx);

                    let iter = hit_comp
                        .matching_permutations(matching_edges.len())
                        .into_iter()
                        .map(move |hit_matched| {
                            let mut instance = instance.clone();
                            for (hit_node, matching_edge) in
                                hit_matched.into_iter().zip(matching_edges.iter())
                            {
                                instance.fix_matching_edge(&matching_edge, idx, hit_node);
                            }
                            instance
                        });

                    Box::new(iter)
                };

            tmp
        }))
    }

    return Box::new(iter);
}
