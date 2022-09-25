use itertools::Itertools;

use crate::{
    path::{
        proof::{Enumerator, EnumeratorTactic},
        AugmentedPathInstance,
    },
    types::Edge,
};

#[derive(Clone)]
pub struct FindMatchingEdgesEnum;

pub struct FindMatchingEdgesEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance> for FindMatchingEdgesEnumerator<'a> {
    fn iter(
        &mut self,
        context: &crate::path::proof::ProofContext,
    ) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        assert!(self.instance.non_path_matching_edges.len() == self.instance.outside_hits().len());

        let path = &self.instance.path;

        let mut left_nodes = vec![
            path[0].get_comp().matching_nodes(),
            path[1].get_comp().matching_nodes(),
        ]
        .concat();
        left_nodes.drain_filter(|node| *node == path[1].get_comp().fixed_node());

        let prelast_nodes = path[context.path_len - 2].get_comp().matching_nodes();
        let last_nodes = path.last_comp().matching_nodes();
        //let first_comp = path[0].get_comp().clone();

        let left_last_crossing = self
            .instance
            .fixed_edge
            .iter()
            .filter(|edge| edge.incident(&left_nodes) && edge.incident(&last_nodes))
            .count();

        let left_prelast_edges = self
            .instance
            .fixed_edge
            .iter()
            .filter(|edge| edge.incident(&left_nodes) && edge.incident(&prelast_nodes))
            .collect_vec();

        let left_used_nodes = left_prelast_edges.iter().map(|e| e.0).collect_vec();
        let prelast_used_nodes = left_prelast_edges.iter().map(|e| e.1).collect_vec();

        let prelast_in = path[2].get_zoomed().in_node.unwrap();
        let free_left = left_nodes
            .into_iter()
            .filter(|n| !left_used_nodes.contains(n))
            .collect_vec();
        let free_prelast = prelast_nodes
            .into_iter()
            .filter(|n| !prelast_used_nodes.contains(n) && *n != &prelast_in)
            .collect_vec();

        if left_last_crossing <= 1 && left_prelast_edges.len() <= 1 {
            let iter = free_prelast.into_iter().flat_map(move |right_matched| {
                let left_used_nodes = left_used_nodes.clone();
                free_left
                    .clone()
                    .into_iter()
                    .filter(move |left| {
                        let c = path[1].get_comp();

                        !(left_used_nodes
                            .iter()
                            .all(|u| c.is_adjacent(u, &c.fixed_node()))
                            && c.is_adjacent(left, &c.fixed_node()))
                    })
                    .map(|left_matched| {
                        let mut new_instance = self.instance.clone();

                        new_instance
                            .fixed_edge
                            .push(Edge(left_matched, *right_matched));

                        new_instance
                    })
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
