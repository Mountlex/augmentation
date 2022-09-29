use itertools::Itertools;

use crate::{
    comps::Node,
    path::{proof::PathContext, AugmentedPathInstance, MatchingEdge, PathHit},
    proof_logic::{Enumerator, EnumeratorTactic},
    types::Edge,
};

#[derive(Clone)]
pub struct FindMatchingEdgesEnum;

pub struct FindMatchingEdgesEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
}

enum Hit {
    Outside,
    Node(Node),
}

impl<'a> Enumerator<AugmentedPathInstance, PathContext> for FindMatchingEdgesEnumerator<'a> {
    fn iter(
        &self,
        context: &PathContext,
    ) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        assert!(
            self.instance.non_path_matching_edges.len() == self.instance.all_outside_hits().len()
        );

        let path = &self.instance.path;

        let mut left_nodes = vec![
            path[0].get_comp().matching_nodes(),
            path[1].get_comp().matching_nodes(),
        ]
        .concat();
        left_nodes.drain_filter(|node| *node == path[1].get_comp().fixed_node());

        let prelast_nodes = path[context.path_len - 2].get_comp().matching_nodes();
        let last_nodes = path.last_comp().possible_in_out_nodes();

        let left_last_crossing = self
            .instance
            .fixed_edge
            .iter()
            .filter(|edge| edge.nodes_incident(&left_nodes) && edge.nodes_incident(&last_nodes))
            .count();

        let left_prelast_edges = self
            .instance
            .fixed_edge
            .iter()
            .filter(|edge| edge.nodes_incident(&left_nodes) && edge.nodes_incident(&prelast_nodes))
            .collect_vec();

        let left_used_nodes = left_prelast_edges.iter().map(|e| e.0).collect_vec();

        let free_left = left_nodes
            .into_iter()
            .filter(|n| !left_used_nodes.contains(n))
            .collect_vec();

        let prelast_matching_endpoints = self
            .instance
            .nodes_with_fixed_edges(2)
            .into_iter()
            .chain(self.instance.outside_edges_on(2).into_iter())
            .sorted()
            .dedup()
            .collect_vec();

        let free_prelast = prelast_nodes
            .into_iter()
            .filter(|n| !prelast_matching_endpoints.contains(n))
            .collect_vec();

        if (left_last_crossing + self.instance.outside_hits_from(3).len() <= 1
            && left_prelast_edges.len() + self.instance.outside_hits_from(2).len() <= 1)
            || prelast_matching_endpoints.len() < 3
        {
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
                    .map(|left| Hit::Node(left))
                    .chain(std::iter::once(Hit::Outside))
                    .map(|left| {
                        let mut new_instance = self.instance.clone();

                        match left {
                            Hit::Outside => new_instance
                                .non_path_matching_edges
                                .push(MatchingEdge::new(2, *right_matched, PathHit::Outside)),
                            Hit::Node(left) => {
                                new_instance.fixed_edge.push(Edge(left, *right_matched))
                            }
                        }

                        new_instance
                    })
            });
            Box::new(iter)
        } else {
            Box::new(vec![self.instance.clone()].into_iter())
        }
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext>
    for FindMatchingEdgesEnum
{
    type Enumer<'a> = FindMatchingEdgesEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        format!("Find more edges")
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        FindMatchingEdgesEnumerator { instance: data }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!(
            "Enumerate more edges: [{}] and [{}]",
            item.fixed_edge.iter().join(", "),
            item.non_path_matching_edges.iter().join(", "),
        )
    }

    fn precondition(
        &self,
        data: &AugmentedPathInstance,
        _context: &PathContext,
    ) -> bool {
        !data.path[0].get_comp().is_large()
            && !data.path[1].get_comp().is_large()
            && !data.path[2].get_comp().is_large()
    }
}
