use itertools::Itertools;

use crate::{
    path::{
        proof::{Enumerator, EnumeratorTactic},
        AugmentedPathInstance,
    },
    types::Edge,
};

pub struct FindMatchingEdgesEnum;

pub struct FindMatchingEdgesEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance> for FindMatchingEdgesEnumerator<'a> {
    fn iter(
        &mut self,
        _context: &crate::path::proof::ProofContext,
    ) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        assert!(self.instance.non_path_matching_edges.len() == self.instance.outside_hits().len());

        let path = &self.instance.path;

        let mut left_nodes = path[0].get_comp().nodes();
        left_nodes.append(&mut path[1].get_comp().nodes());
        left_nodes.drain_filter(|node| *node == path[1].get_comp().fixed_node());

        let last_nodes = path.last_comp().nodes();
        //let first_comp = path[0].get_comp().clone();

        let num_crossing = self
            .instance
            .fixed_edge
            .iter()
            .filter(|edge| edge.incident(&left_nodes) && edge.incident(&last_nodes))
            .count();

        if num_crossing <= 1 {
            let prelast_in = path[2].get_zoomed().in_node.unwrap();
            let iter = path[2]
                .get_comp()
                .matching_permutations(2 - num_crossing)
                .into_iter()
                .filter(move |right_matched| !right_matched.contains(&prelast_in))
                .flat_map(move |right_matched| {
                    left_nodes
                        .iter()
                        .permutations(2 - num_crossing)
                        .filter(|left_matched| {
                            left_matched.iter().any(|&l| {
                                !path[1]
                                    .get_comp()
                                    .is_adjacent(path[1].get_comp().fixed_node(), *l)
                            })
                        })
                        .map(|left_matched| {
                            let mut new_instance = self.instance.clone();
                            for (left, right) in left_matched.into_iter().zip(right_matched.iter())
                            {
                                new_instance.fixed_edge.push(Edge(*left, *right));
                            }
                            new_instance
                        })
                        .collect_vec()
                });
            Box::new(iter)
        } else {
            Box::new(vec![self.instance.clone()].into_iter())
        }
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance> for FindMatchingEdgesEnum {
    type Enumer<'a> = FindMatchingEdgesEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        format!("Find more edges")
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        FindMatchingEdgesEnumerator { instance: data }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!(
            "Enumerate more matching edges [{}]",
            item.fixed_edge.iter().join(", ")
        )
    }
}
