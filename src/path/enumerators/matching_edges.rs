use itertools::Itertools;

use crate::{
    comps::Component,
    path::{
        proof::PathContext, tactics::contract::check_for_comp, AbstractEdge, AugmentedPathInstance,
        PathHit, Pidx,
    },
    proof_logic::{OptEnumerator, OptEnumeratorTactic},
    types::Edge,
    Node,
};

#[derive(Clone)]
pub struct FindMatchingEdgesEnum {
    path_finite: bool,
}

impl FindMatchingEdgesEnum {
    pub fn new(path_finite: bool) -> Self {
        Self { path_finite }
    }
}

pub struct FindMatchingEdgesEnumerator<'a> {
    instance: &'a AugmentedPathInstance,
    path_finite: bool,
}

enum Hit {
    Outside,
    Node(Node),
}

impl<'a> OptEnumerator<AugmentedPathInstance, PathContext> for FindMatchingEdgesEnumerator<'a> {
    fn iter(
        &self,
        _context: &PathContext,
    ) -> Option<Box<dyn Iterator<Item = AugmentedPathInstance> + '_>> {
        assert!(self.instance.abstract_edges.len() == self.instance.all_outside_hits().len());

        if self.path_finite {
            if let Some(iter) = infinite_path_matching_edges(self.instance) {
                return Some(iter);
            }
            if let Some(iter) = finite_path_matching_edges(self.instance) {
                return Some(iter);
            }
            contractable_path_matching_edges(self.instance)
        } else {
            if let Some(iter) = infinite_path_matching_edges(self.instance) {
                return Some(iter);
            }
            contractable_path_matching_edges(self.instance)

        }
    }
}

fn contractable_path_matching_edges(
    instance: &AugmentedPathInstance,
) -> Option<Box<dyn Iterator<Item = AugmentedPathInstance> + '_>> {
    let instance = instance;

    for i in 1..instance.path_len() {
        let node_idx = Pidx::from(i);
        let node = &instance[node_idx];
        let res = check_for_comp(
            instance,
            node.get_comp(),
            node.get_zoomed(),
            node.path_idx(),
        );
        if res.success() {
            let free_nodes = instance.nodes_without_edges(node_idx);

            let rem_nodes = instance
                .nodes
                .iter()
                .filter(|n| n.path_idx().raw() != i)
                .flat_map(|n| n.get_comp().matching_nodes())
                .cloned()
                .collect_vec();

            let iter = free_nodes.into_iter().flat_map(move |node_matched| {
                let mut rem_iter: Box<dyn Iterator<Item = Hit>> = Box::new(
                    rem_nodes
                        .clone().into_iter()
                        .map(|left| Hit::Node(left)),
                );

                for i_rem in 0..instance.path_len() {
                    if i_rem != i {
                        if let Component::Large(n) = instance[Pidx::N(i_rem)].get_comp() {
                            rem_iter = Box::new(rem_iter.chain(std::iter::once(Hit::Node(*n))));
                        }
                    }
                }

                rem_iter = Box::new(rem_iter.chain(std::iter::once(Hit::Outside)));

                rem_iter.map(move |rem_hit| {
                    let mut new_instance = instance.clone();

                    match rem_hit {
                        Hit::Outside => new_instance.abstract_edges.push(AbstractEdge::new(
                            node_idx,
                            node_matched,
                            PathHit::Outside,
                        )),
                        Hit::Node(left) => {
                            let left_idx = new_instance.index_of_super_node(left);
                            new_instance.fixed_edges.push(Edge::new(
                                left,
                                left_idx,
                                node_matched,
                                node_idx,
                            ))
                        }
                    }

                    new_instance
                })
            });
            return Some(Box::new(iter));
        }
    }

    None
}

fn finite_path_matching_edges(
    instance: &AugmentedPathInstance,
) -> Option<Box<dyn Iterator<Item = AugmentedPathInstance> + '_>> {
    let instance = instance;

    if let Some(iter) = infinite_path_matching_edges(instance) {
        return Some(iter);
    }

    let mut bound = 2;
    while bound <= 3 {
        for i in 1..instance.path_len() {
            let node_idx = Pidx::from(i);
            let node_matching_endpoints = instance
                .nodes_with_fixed_edges(node_idx)
                .into_iter()
                .chain(instance.outside_edges_on(node_idx).into_iter())
                .unique()
                .collect_vec();

            if node_matching_endpoints.len() < bound {
                let mut node_free = instance[node_idx]
                    .get_comp()
                    .matching_nodes()
                    .into_iter()
                    .filter(|n| !node_matching_endpoints.contains(n))
                    .collect_vec();
                if let Component::Large(n) = instance[node_idx].get_comp() {
                    node_free.push(n);
                }

                let rem_nodes = instance
                    .nodes
                    .iter()
                    .filter(|n| n.path_idx().raw() != i)
                    .flat_map(|n| n.get_comp().matching_nodes())
                    .cloned()
                    .filter(|n| {
                        if i == instance.path_len() - 1 {
                            *n != instance[Pidx::from(i - 1)].get_zoomed().in_node.unwrap()
                        } else if i == 0 {
                            *n != instance[Pidx::from(i + 1)].get_zoomed().out_node.unwrap()
                        } else {
                            *n != instance[Pidx::from(i + 1)].get_zoomed().out_node.unwrap()
                                && *n != instance[Pidx::from(i - 1)].get_zoomed().in_node.unwrap()
                        }
                    })
                    .collect_vec();

                let node_rem_crossing = instance
                    .fixed_edges
                    .iter()
                    .filter(|edge| {
                        edge.nodes_incident(&rem_nodes)
                            && edge.nodes_incident(&instance[node_idx].get_comp().matching_nodes())
                    })
                    .collect_vec();

                let rem_used_nodes = rem_nodes
                    .iter()
                    .filter(|n| node_rem_crossing.iter().any(|e| e.node_incident(n)))
                    .cloned()
                    .collect_vec();

                let rem_free = rem_nodes
                    .into_iter()
                    .filter(|n| !rem_used_nodes.contains(n))
                    .collect_vec();

                let iter = node_free.into_iter().flat_map(move |node_matched| {
                    let rem_used_nodes = rem_used_nodes.clone();
                    let mut rem_iter: Box<dyn Iterator<Item = Hit>> = Box::new(
                        rem_free
                            .clone()
                            .into_iter()
                            .filter(move |left| {
                                let c = instance[node_idx].get_comp();

                                !(rem_used_nodes.iter().all(|u| {
                                    c.is_adjacent(
                                        u,
                                        &instance[node_idx].get_zoomed().out_node.unwrap(),
                                    )
                                }) && c.is_adjacent(
                                    left,
                                    &instance[node_idx].get_zoomed().out_node.unwrap(),
                                ))
                            })
                            .map(|left| Hit::Node(left)),
                    );

                    for i_rem in 0..instance.path_len() {
                        if i_rem != i {
                            if let Component::Large(n) = instance[Pidx::N(i_rem)].get_comp() {
                                rem_iter = Box::new(rem_iter.chain(std::iter::once(Hit::Node(*n))));
                            }
                        }
                    }

                    rem_iter = Box::new(rem_iter.chain(std::iter::once(Hit::Outside)));

                    rem_iter.map(move |rem_hit| {
                        let mut new_instance = instance.clone();

                        match rem_hit {
                            Hit::Outside => new_instance.abstract_edges.push(AbstractEdge::new(
                                node_idx,
                                *node_matched,
                                PathHit::Outside,
                            )),
                            Hit::Node(left) => {
                                let left_idx = new_instance.index_of_super_node(left);
                                new_instance.fixed_edges.push(Edge::new(
                                    left,
                                    left_idx,
                                    *node_matched,
                                    node_idx,
                                ))
                            }
                        }

                        new_instance
                    })
                });
                return Some(Box::new(iter));
            }
        }

        bound += 1;
    }

    None
}

fn infinite_path_matching_edges(
    instance: &AugmentedPathInstance,
) -> Option<Box<dyn Iterator<Item = AugmentedPathInstance> + '_>> {
    let instance = instance;

    for i in 1..instance.path_len() - 2 {
        let node_idx = Pidx::from(i);
        let node_matching_endpoints = instance
            .nodes_with_fixed_edges(node_idx)
            .into_iter()
            .chain(instance.outside_edges_on(node_idx).into_iter())
            .unique()
            .collect_vec();
        let mut node_free = instance[node_idx]
            .get_comp()
            .matching_nodes()
            .into_iter()
            .filter(|n| !node_matching_endpoints.contains(n))
            .collect_vec();
        if let Component::Large(n) = instance[node_idx].get_comp() {
            node_free.push(n);
        }

        let rem_nodes = instance
            .nodes
            .split_at(i + 1)
            .1
            .iter()
            .flat_map(|n| n.get_comp().matching_nodes())
            .cloned()
            .filter(|n| *n != instance[Pidx::from(i + 1)].get_zoomed().out_node.unwrap())
            .collect_vec();

        let prefix_nodes = instance
            .nodes
            .split_at(i)
            .0
            .iter()
            .flat_map(|n| n.get_comp().matching_nodes())
            .cloned()
            .collect_vec();

        let prefix_rem_crossing = instance
            .fixed_edges
            .iter()
            .filter(|edge| edge.nodes_incident(&rem_nodes) && edge.nodes_incident(&prefix_nodes))
            .collect_vec();

        let rem_used_nodes = rem_nodes
            .iter()
            .filter(|n| prefix_rem_crossing.iter().any(|e| e.node_incident(n)))
            .cloned()
            .collect_vec();

        let rem_free = rem_nodes
            .into_iter()
            .filter(|n| !rem_used_nodes.contains(n))
            .collect_vec();

        let prefix_outside: usize = Pidx::range(i)
            .iter()
            .map(|idx| instance.outside_hits_from(*idx).len())
            .sum();

        if (prefix_rem_crossing.len() + prefix_outside <= 1) || node_matching_endpoints.len() < 3 {
            let iter = node_free.into_iter().flat_map(move |node_matched| {
                let rem_used_nodes = rem_used_nodes.clone();
                let mut rem_iter: Box<dyn Iterator<Item = Hit>> = Box::new(
                    rem_free
                        .clone()
                        .into_iter()
                        .filter(move |left| {
                            let c = instance[node_idx].get_comp();

                            !(rem_used_nodes.iter().all(|u| {
                                c.is_adjacent(u, &instance[node_idx].get_zoomed().out_node.unwrap())
                            }) && c.is_adjacent(
                                left,
                                &instance[node_idx].get_zoomed().out_node.unwrap(),
                            ))
                        })
                        .map(|left| Hit::Node(left)),
                );

                for i_rem in i + 1..instance.path_len() {
                    if let Component::Large(n) = instance[Pidx::N(i_rem)].get_comp() {
                        rem_iter = Box::new(rem_iter.chain(std::iter::once(Hit::Node(*n))));
                    }
                }

                if node_matching_endpoints.len() < 3 {
                    rem_iter = Box::new(rem_iter.chain(std::iter::once(Hit::Outside)));
                };

                rem_iter.map(move |rem_hit| {
                    let mut new_instance = instance.clone();

                    match rem_hit {
                        Hit::Outside => new_instance.abstract_edges.push(AbstractEdge::new(
                            node_idx,
                            *node_matched,
                            PathHit::Outside,
                        )),
                        Hit::Node(left) => {
                            let left_idx = new_instance.index_of_super_node(left);
                            new_instance.fixed_edges.push(Edge::new(
                                left,
                                left_idx,
                                *node_matched,
                                node_idx,
                            ))
                        }
                    }

                    new_instance
                })
            });
            return Some(Box::new(iter));
        }
    }

    None
}

impl OptEnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext>
    for FindMatchingEdgesEnum
{
    type Enumer<'a> = FindMatchingEdgesEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        String::new()
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        FindMatchingEdgesEnumerator {
            instance: data,
            path_finite: self.path_finite,
        }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!(
            "Enumerate more edges: [{}] and [{}]",
            item.fixed_edges.iter().join(", "),
            item.abstract_edges.iter().join(", "),
        )
    }

    fn precondition(&self, _data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        true
    }
}
