use itertools::Itertools;

use crate::{
    comps::{Component, Node},
    path::{
        proof::{Enumerator, EnumeratorTactic},
        AugmentedPathInstance, NicePairConfig, SelectedHitInstance, SuperNode, ZoomedNode,
    },
};

pub struct ExpandEnum;
pub struct ExpandLastEnum;

pub struct ExpandEnumerator<'a> {
    pub instance: &'a AugmentedPathInstance,
    pub hit_comp_idx: usize,
}

impl<'a> ExpandEnumerator<'a> {
    pub fn new(instance: &'a AugmentedPathInstance, hit_comp_idx: usize) -> Self {
        Self {
            instance,
            hit_comp_idx,
        }
    }
}

impl<'a> Enumerator<SelectedHitInstance> for ExpandEnumerator<'a> {
    fn iter(
        &mut self,
        context: &crate::path::proof::ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedHitInstance> + '_> {
        let hit_comp_idx = self.hit_comp_idx;
        let iter = Enumerator::<AugmentedPathInstance>::iter(self, context).map(move |aug| {
            SelectedHitInstance {
                instance: aug,
                hit_comp_idx,
            }
        });

        Box::new(iter)
    }
}

impl<'a> Enumerator<AugmentedPathInstance> for ExpandEnumerator<'a> {
    fn iter(
        &mut self,
        context: &crate::path::proof::ProofContext,
    ) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let path_len = context.path_len;
        let node_idx = self.hit_comp_idx;
        let instance = self.instance;
        let path = &instance.path;
        let node = &path[node_idx];
        let comp = node.get_comp();

        let mut connected_nodes = comp
            .nodes()
            .iter()
            .filter(|&n| {
                instance.fixed_edge.iter().any(|e| *n == e.0 || *n == e.1)
                    || instance
                        .non_path_matching_edges
                        .iter()
                        .any(|e| e.source() == *n)
            })
            .cloned()
            .collect_vec();

            
        if node.is_zoomed() {
            if let Some(in_node) = node.get_zoomed().in_node {
                connected_nodes.push(in_node);            
            } 
            if let Some(out_node) = node.get_zoomed().out_node {
                connected_nodes.push(out_node);            
            } 
            connected_nodes.sort();
            connected_nodes.dedup();

            // node is already zoomed, just update nice pairs of new incident edges
            let iter = comp_npcs(
                node,
                &connected_nodes,
                &node.get_zoomed().npc,
                &node.get_zoomed().connected_nodes,
            )
            .into_iter()
            .map(move |npc| {
                let mut path_clone = path.clone();
                let mut zoomed_node = path_clone[node_idx].get_zoomed_mut();
                zoomed_node.npc = npc;
                zoomed_node.connected_nodes = connected_nodes.clone();

                AugmentedPathInstance {
                    path: path_clone,
                    non_path_matching_edges: instance.non_path_matching_edges.clone(),
                    fixed_edge: instance.fixed_edge.clone(),
                }
            });
            Box::new(iter)
        } else {
            // this will be out
            connected_nodes.push(comp.fixed_node());

            let in_node_iter: Box<dyn Iterator<Item = Node>> = if node_idx < path_len - 1 {
                // enumerate all ins
                Box::new(comp.nodes().into_iter().filter(|n| *n != comp.fixed_node()))
            } else {
                Box::new(vec![comp.fixed_node()].into_iter())
            };

            let iter = in_node_iter.flat_map(move |in_node| {
                let mut nodes = connected_nodes.clone();
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
                        node,
                        &nodes,
                        &NicePairConfig {
                            nice_pairs: vec![(comp.fixed_node(), in_node)],
                        },
                        &vec![comp.fixed_node(), in_node],
                    )
                } else {
                    comp_npcs(node, &nodes, &NicePairConfig::empty(), &vec![])
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
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance> for ExpandLastEnum {
    type Enumer<'a> = ExpandEnumerator<'a>;

    fn msg(&self, _data: &AugmentedPathInstance) -> String {
        format!("Expand last node")
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        ExpandEnumerator {
            instance: data,
            hit_comp_idx: data.path.nodes.len() - 1,
        }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Expanded {}", item.path.nodes.last().unwrap())
    }
}

impl EnumeratorTactic<SelectedHitInstance, SelectedHitInstance> for ExpandEnum {
    type Enumer<'a> = ExpandEnumerator<'a>;

    fn msg(&self, data: &SelectedHitInstance) -> String {
        format!("Expand node {}", data.hit_comp_idx)
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        ExpandEnumerator {
            instance: &data.instance,
            hit_comp_idx: data.hit_comp_idx,
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
        Component::Cycle(_) => {
            nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
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
                .sorted()
                .dedup()
                .collect_vec()
        }
        Component::Large(_) => vec![NicePairConfig::empty()],
        Component::Complex(_, black, _) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(&v2))
                .collect_vec(),
        }],
    }
}
