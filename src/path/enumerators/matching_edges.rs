use itertools::Itertools;

use crate::{
    comps::Component,
    path::{proof::PathContext, AugmentedPathInstance, MatchingEdge, PathHit, Pidx},
    proof_logic::{Enumerator, EnumeratorTactic},
    types::Edge,
    Node,
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
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        assert!(
            self.instance.non_path_matching_edges.len() == self.instance.all_outside_hits().len()
        );

        let instance = self.instance;
        let prelast_nodes = instance[Pidx::Prelast].get_comp().matching_nodes();

        // first prelast 3-matching
        let prelast_matching_endpoints = self
            .instance
            .nodes_with_fixed_edges(Pidx::Prelast)
            .into_iter()
            .chain(self.instance.outside_edges_on(Pidx::Prelast).into_iter())
            .unique()
            .collect_vec();

        let mut free_prelast = prelast_nodes
            .into_iter()
            .filter(|n| !prelast_matching_endpoints.contains(n))
            .collect_vec();
        if let Component::Large(n) = instance[Pidx::Prelast].get_comp() {
            free_prelast.push(n);
        }

        let mut left_nodes = instance
            .nodes
            .split_at(2)
            .1
            .iter()
            .flat_map(|n| n.get_comp().matching_nodes())
            .cloned()
            .collect_vec();
        left_nodes
            .drain_filter(|node| *node == instance[Pidx::N(2)].get_zoomed().out_node.unwrap());

        let last_nodes = instance[Pidx::Last].get_comp().possible_in_out_nodes();

        let left_last_edges = self
            .instance
            .fixed_edge
            .iter()
            .filter(|edge| edge.nodes_incident(&left_nodes) && edge.nodes_incident(&last_nodes))
            .collect_vec();

        let num_left_last_crossing = left_last_edges.len();

        let left_prelast_edges = self
            .instance
            .fixed_edge
            .iter()
            .filter(|edge| edge.nodes_incident(&left_nodes) && edge.nodes_incident(&prelast_nodes))
            .collect_vec();

        let left_used_nodes = left_nodes
            .iter()
            .filter(|n| {
                left_prelast_edges.iter().any(|e| e.node_incident(n))
                    || left_last_edges.iter().any(|e| e.node_incident(n))
            })
            .cloned()
            .collect_vec();

        let free_left = left_nodes
            .into_iter()
            .filter(|n| !left_used_nodes.contains(n))
            .collect_vec();

        let prelast_matching_endpoints = self
            .instance
            .nodes_with_fixed_edges(Pidx::Prelast)
            .into_iter()
            .chain(self.instance.outside_edges_on(Pidx::Prelast).into_iter())
            .unique()
            .collect_vec();

        if (num_left_last_crossing
            + left_prelast_edges.len()
            + self.instance.outside_hits_from(Pidx::Last).len()
            + self.instance.outside_hits_from(Pidx::Prelast).len()
            <= 1)
            || prelast_matching_endpoints.len() < 3
        {
            let iter = free_prelast.into_iter().flat_map(move |right_matched| {
                let left_used_nodes = left_used_nodes.clone();
                let mut left_iter: Box<dyn Iterator<Item = Hit>> = Box::new(
                    free_left
                        .clone()
                        .into_iter()
                        .filter(move |left| {
                            let c = instance[Pidx::N(2)].get_comp();

                            !(left_used_nodes.iter().all(|u| {
                                c.is_adjacent(
                                    u,
                                    &instance[Pidx::N(2)].get_zoomed().out_node.unwrap(),
                                )
                            }) && c.is_adjacent(
                                left,
                                &instance[Pidx::N(2)].get_zoomed().out_node.unwrap(),
                            ))
                        })
                        .map(|left| Hit::Node(left)),
                );
                if let Component::Large(n) = instance[Pidx::N(3)].get_comp() {
                    left_iter = Box::new(left_iter.chain(std::iter::once(Hit::Node(*n))));
                }
                if let Component::Large(n) = instance[Pidx::N(2)].get_comp() {
                    left_iter = Box::new(left_iter.chain(std::iter::once(Hit::Node(*n))));
                }

                if prelast_matching_endpoints.len() < 3 {
                    left_iter = Box::new(left_iter.chain(std::iter::once(Hit::Outside)));
                };

                left_iter.map(|left| {
                    let mut new_instance = self.instance.clone();

                    match left {
                        Hit::Outside => new_instance.non_path_matching_edges.push(
                            MatchingEdge::new(Pidx::Prelast, *right_matched, PathHit::Outside),
                        ),
                        Hit::Node(left) => {
                            let left_idx = instance.index_of_super_node(left);
                            new_instance.fixed_edge.push(Edge::new(
                                left,
                                left_idx,
                                *right_matched,
                                Pidx::Prelast,
                            ))
                        }
                    }

                    new_instance
                })
            });
            return Box::new(iter);
        }

        if self.instance.path_len() == 5 {
            let instance = self.instance;
            let n2_nodes = instance[Pidx::N(2)].get_comp().matching_nodes();

            // first prelast 3-matching
            let n2_matching_endpoints = self
                .instance
                .nodes_with_fixed_edges(Pidx::N(2))
                .into_iter()
                .chain(self.instance.outside_edges_on(Pidx::N(2)).into_iter())
                .unique()
                .collect_vec();

            let mut free_n2 = n2_nodes
                .into_iter()
                .filter(|n| !n2_matching_endpoints.contains(n))
                .collect_vec();
            if let Component::Large(n) = instance[Pidx::N(2)].get_comp() {
                free_n2.push(n);
            }

            let mut left_nodes = instance
                .nodes
                .split_at(3)
                .1
                .iter()
                .flat_map(|n| n.get_comp().matching_nodes())
                .cloned()
                .collect_vec();
            left_nodes
                .drain_filter(|node| *node == instance[Pidx::N(3)].get_zoomed().out_node.unwrap());

            
            let last_nodes = instance[Pidx::Last].get_comp().possible_in_out_nodes();
            let left_last_edges = self
                .instance
                .fixed_edge
                .iter()
                .filter(|edge| edge.nodes_incident(&left_nodes) && edge.nodes_incident(&last_nodes))
                .collect_vec();

            let num_left_last_crossing = left_last_edges.len();

            let prelast_nodes = instance[Pidx::Prelast].get_comp().possible_in_out_nodes();
            let left_prelast_edges = self
                .instance
                .fixed_edge
                .iter()
                .filter(|edge| {
                    edge.nodes_incident(&left_nodes) && edge.nodes_incident(&prelast_nodes)
                })
                .collect_vec();
            let num_left_prelast_crossing = left_prelast_edges.len();


            let left_n2_edges = self
                .instance
                .fixed_edge
                .iter()
                .filter(|edge| {
                    edge.nodes_incident(&left_nodes) && edge.nodes_incident(&n2_nodes)
                })
                .collect_vec();

            let left_used_nodes = left_nodes
                .iter()
                .filter(|n| {
                    left_prelast_edges.iter().any(|e| e.node_incident(n))
                        || left_last_edges.iter().any(|e| e.node_incident(n))
                        || left_n2_edges.iter().any(|e| e.node_incident(n))
                })
                .cloned()
                .collect_vec();

            let free_left = left_nodes
                .into_iter()
                .filter(|n| !left_used_nodes.contains(n))
                .collect_vec();

            let n2_matching_endpoints = self
                .instance
                .nodes_with_fixed_edges(Pidx::N(2))
                .into_iter()
                .chain(self.instance.outside_edges_on(Pidx::N(2)).into_iter())
                .unique()
                .collect_vec();

            if (num_left_last_crossing
                + num_left_prelast_crossing
                + left_n2_edges.len()
                + self.instance.outside_hits_from(Pidx::Last).len()
                + self.instance.outside_hits_from(Pidx::Prelast).len()
                + self.instance.outside_hits_from(Pidx::N(2)).len()
                <= 1)
                || n2_matching_endpoints.len() < 3
            {
                let iter = free_n2.into_iter().flat_map(move |right_matched| {
                    let left_used_nodes = left_used_nodes.clone();
                    let mut left_iter: Box<dyn Iterator<Item = Hit>> = Box::new(
                        free_left
                            .clone()
                            .into_iter()
                            .filter(move |left| {
                                let c = instance[Pidx::N(2)].get_comp();

                                !(left_used_nodes.iter().all(|u| {
                                    c.is_adjacent(
                                        u,
                                        &instance[Pidx::N(2)].get_zoomed().out_node.unwrap(),
                                    )
                                }) && c.is_adjacent(
                                    left,
                                    &instance[Pidx::N(2)].get_zoomed().out_node.unwrap(),
                                ))
                            })
                            .map(|left| Hit::Node(left)),
                    );
                    if let Component::Large(n) = instance[Pidx::N(4)].get_comp() {
                        left_iter = Box::new(left_iter.chain(std::iter::once(Hit::Node(*n))));
                    }
                    if let Component::Large(n) = instance[Pidx::N(3)].get_comp() {
                        left_iter = Box::new(left_iter.chain(std::iter::once(Hit::Node(*n))));
                    }
                    if let Component::Large(n) = instance[Pidx::N(2)].get_comp() {
                        left_iter = Box::new(left_iter.chain(std::iter::once(Hit::Node(*n))));
                    }

                    if prelast_matching_endpoints.len() < 3 {
                        left_iter = Box::new(left_iter.chain(std::iter::once(Hit::Outside)));
                    };

                    left_iter.map(|left| {
                        let mut new_instance = self.instance.clone();

                        match left {
                            Hit::Outside => new_instance.non_path_matching_edges.push(
                                MatchingEdge::new(Pidx::N(2), *right_matched, PathHit::Outside),
                            ),
                            Hit::Node(left) => {
                                let left_idx = instance.index_of_super_node(left);
                                new_instance.fixed_edge.push(Edge::new(
                                    left,
                                    left_idx,
                                    *right_matched,
                                    Pidx::N(2),
                                ))
                            }
                        }

                        new_instance
                    })
                });
                return Box::new(iter);
            }
        }

        Box::new(vec![self.instance.clone()].into_iter())
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext>
    for FindMatchingEdgesEnum
{
    type Enumer<'a> = FindMatchingEdgesEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        String::new()
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

    fn precondition(&self, _data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        true
    }
}
