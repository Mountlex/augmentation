use itertools::Itertools;

use crate::{
    path::comps::{Component, Node},
    path::{
        proof::PathContext, AugmentedPathInstance, NicePairConfig, SelectedHitInstance, SuperNode,
        ZoomedNode,
    },
    proof_logic::{Enumerator, EnumeratorTactic},
};

#[derive(Clone)]
pub struct ExpandEnum;
#[derive(Clone)]
pub struct ExpandLastEnum;

pub struct ExpandEnumerator<'a> {
    pub instance: &'a AugmentedPathInstance,
    pub hit_comp_idx: usize,
    pub last_hit: bool,
}

impl<'a> ExpandEnumerator<'a> {
    pub fn _new(instance: &'a AugmentedPathInstance, hit_comp_idx: usize, last_hit: bool) -> Self {
        Self {
            instance,
            hit_comp_idx,
            last_hit,
        }
    }
}

impl<'a> Enumerator<SelectedHitInstance, PathContext> for ExpandEnumerator<'a> {
    fn iter(
        &self,
        context: &crate::path::proof::PathContext,
    ) -> Box<dyn Iterator<Item = SelectedHitInstance> + '_> {
        let hit_comp_idx = self.hit_comp_idx;
        let last_hit = self.last_hit;
        let iter =
            Enumerator::<AugmentedPathInstance, PathContext>::iter(self, context).map(move |aug| {
                SelectedHitInstance {
                    instance: aug,
                    hit_comp_idx,
                    last_hit,
                }
            });

        Box::new(iter)
    }
}

pub fn expand_iter(
    instance: AugmentedPathInstance,
    node_idx: usize,
    context: PathContext,
) -> Box<dyn Iterator<Item = AugmentedPathInstance>> {
    let path_len = context.path_len;
    let path = instance.path.clone();
    let node = path[node_idx].clone();
    let comp = node.get_comp().clone();

    let mut updated_nodes_with_edges = instance.nodes_with_edges(node_idx);

    if node.is_zoomed() {
        let comp_conn_nodes = &node.get_zoomed().connected_nodes;

        if comp_conn_nodes != &updated_nodes_with_edges {
            // node is already zoomed, just update nice pairs of new incident edges
            let iter = comp_npcs(
                &node,
                &updated_nodes_with_edges,
                &node.get_zoomed().npc,
                &comp_conn_nodes,
            )
            .into_iter()
            .map(move |npc| {
                let mut path_clone = path.clone();
                let mut zoomed_node = path_clone[node_idx].get_zoomed_mut();
                zoomed_node.npc = npc;
                zoomed_node.connected_nodes = updated_nodes_with_edges.clone();

                AugmentedPathInstance {
                    path: path_clone,
                    non_path_matching_edges: instance.non_path_matching_edges.clone(),
                    fixed_edge: instance.fixed_edge.clone(),
                }
            });
            Box::new(iter)
        } else {
            Box::new(vec![instance].into_iter())
        }
    } else {
        // this will be out
        updated_nodes_with_edges.push(comp.fixed_node());

        let in_node_iter = if node_idx < path_len - 1 {
            // enumerate all ins
            let comp_clone = comp.clone();
            Box::new(
                comp_clone
                    .possible_in_out_nodes()
                    .into_iter()
                    .filter(|n| valid_in_out(&comp, **n, comp.fixed_node(), node_idx == path_len - 2, node.used()))
                    .cloned()
                    .collect_vec(),
            )
        } else {
            Box::new(vec![comp.fixed_node()])
        };

        let iter = in_node_iter.into_iter().flat_map(move |in_node| {
            let mut nodes = updated_nodes_with_edges.clone();
            nodes.push(in_node);
            nodes.sort();
            nodes.dedup();

            let npcs = if node_idx < path_len - 1
                && (comp.is_complex()
                    || comp.is_c3()
                    || comp.is_c4()
                    || (comp.is_c5() && !node.used()))
            {
                comp_npcs(
                    &node,
                    &nodes,
                    &NicePairConfig {
                        nice_pairs: vec![(comp.fixed_node(), in_node)],
                    },
                    &vec![comp.fixed_node(), in_node],
                )
            } else {
                comp_npcs(&node, &nodes, &NicePairConfig::empty(), &vec![])
            };

            npcs.into_iter()
                .map(|npc| {
                    let mut path_clone = path.clone();
                    path_clone[node_idx] = SuperNode::Zoomed(ZoomedNode {
                        comp: comp.clone(),
                        npc,
                        in_node: Some(in_node),
                        out_node: if node_idx < path_len - 1 {
                            Some(comp.fixed_node())
                        } else {
                            None
                        },
                        connected_nodes: nodes.clone(),
                        used: node.get_abstract().used,
                    });

                    AugmentedPathInstance {
                        path: path_clone,
                        non_path_matching_edges: instance.non_path_matching_edges.clone(),
                        fixed_edge: instance.fixed_edge.clone(),
                    }
                })
                .collect_vec()
        });
        Box::new(iter)
    }
}

impl<'a> Enumerator<AugmentedPathInstance, PathContext> for ExpandEnumerator<'a> {
    fn iter(&self, context: &PathContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        expand_iter(self.instance.clone(), self.hit_comp_idx, context.clone())
    }
}

fn valid_in_out(c: &Component, new_in: Node, new_out: Node, prelast: bool, used: bool) -> bool {
    if c.is_c3() || c.is_c4() || c.is_complex() || (c.is_c5() && prelast && used) {
        new_in != new_out
    } else {
        true
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext>
    for ExpandLastEnum
{
    type Enumer<'a> = ExpandEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        format!("Expand last node")
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        ExpandEnumerator {
            instance: data,
            hit_comp_idx: data.path.nodes.len() - 1,
            last_hit: false,
        }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Expanded {}", item.path.nodes.last().unwrap())
    }
}

impl EnumeratorTactic<SelectedHitInstance, SelectedHitInstance, PathContext> for ExpandEnum {
    type Enumer<'a> = ExpandEnumerator<'a>;

    fn msg(&self, data: &SelectedHitInstance) -> String {
        format!("Expand node {}", data.hit_comp_idx)
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        ExpandEnumerator {
            instance: &data.instance,
            hit_comp_idx: data.hit_comp_idx,
            last_hit: data.last_hit,
        }
    }

    fn item_msg(&self, item: &SelectedHitInstance) -> String {
        format!("Expanded node {}", item.instance.path[item.hit_comp_idx])
    }
}

fn comp_npcs(
    node: &SuperNode,
    nodes: &[Node],
    consistent_npc: &NicePairConfig,
    consistent_nodes: &[Node],
) -> Vec<NicePairConfig> {
    let comp = node.get_comp();

    match comp {
        Component::Large(_) => vec![NicePairConfig::empty()],
        Component::ComplexTree(_, black) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(&v2))
                .collect_vec(),
        }],
        Component::ComplexPath(_, black) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(&v2))
                .collect_vec(),
        }],
        _ => {
            // cycle case
            nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(u,v)| !comp.is_adjacent(u, v))
                .powerset()
                .map(|config| NicePairConfig { nice_pairs: config })
                // .filter(|npc| {
                //     // if config misses a nice pair although it is a pair of adjacent vertices, remove it
                //     adj_pairs.iter().all(|(u, v)| npc.is_nice_pair(*u, *v))
                // })
                .map(|mut npc| {
                    // adjacent vertices are always nice pairs!
                    npc.nice_pairs.append(&mut comp.edges());
                    npc
                })
                .filter(|npc| npc.is_consistent_with(&consistent_npc, &consistent_nodes))
                //.sorted()
                //.dedup()
                .collect_vec()
        }
    }
}
