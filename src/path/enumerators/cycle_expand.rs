use itertools::Itertools;

use crate::{
    path::{
        proof::{Enumerator, EnumeratorTactic},
        AugmentedPathInstance, NicePairConfig, PathInstance, SuperNode, ZoomedNode,
    },
    types::Edge,
};

use super::nice_pairs::comp_npcs;

pub struct CycleExpanderEnumTactic;

pub struct CycleExpanderEnumerator<'a> {
    input: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<AugmentedPathInstance> for CycleExpanderEnumerator<'a> {
    fn iter(
        &mut self,
        context: &mut crate::path::proof::ProofContext,
    ) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let path = &self.input.path;
        let fixed_edges = self.input.fixed_edge.clone();
        let path_len = context.path_len;

        let mut paths: Vec<PathInstance> = vec![];

        path.nodes.iter().enumerate().for_each(|(idx, node)| {
            let fixed_edges = fixed_edges.clone();
            paths = paths
                .iter()
                .flat_map(move |p| {
                    let edge_hit_nodes = node
                        .get_comp()
                        .nodes()
                        .iter()
                        .filter(|&n| fixed_edges.iter().any(|e| *n == e.0 || *n == e.1))
                        .cloned()
                        .collect_vec();

                    if let SuperNode::Abstract(abs) = node {
                        let abs_comp = abs.get_comp();
                        let np = abs_comp.is_c3()
                            || abs_comp.is_c4()
                            || (abs_comp.is_c5() && !abs.used)
                            || abs_comp.is_complex();

                        if idx == 0 {
                            abs.get_comp()
                                .nodes()
                                .into_iter()
                                .flat_map(|out| {
                                    let mut nodes = edge_hit_nodes.clone();
                                    nodes.push(out);
                                    nodes.sort();
                                    nodes.dedup();

                                    comp_npcs(node.get_comp(), &nodes)
                                        .into_iter()
                                        .map(move |npc| {
                                            let mut new_path = p.clone();
                                            new_path.nodes[idx] = SuperNode::Zoomed(ZoomedNode {
                                                comp: abs.get_comp().clone(),
                                                npc,
                                                in_node: None,
                                                out_node: Some(out),
                                                used: abs.used,
                                            });
                                            new_path
                                        })
                                        .collect_vec()
                                })
                                .collect_vec()
                        } else {
                            abs.get_comp()
                                .matching_permutations(2)
                                .into_iter()
                                .flat_map(|in_out| {
                                    let mut nodes = edge_hit_nodes.clone();
                                    nodes.push(in_out[0]);
                                    nodes.push(in_out[1]);
                                    nodes.sort();
                                    nodes.dedup();

                                    comp_npcs(node.get_comp(), &nodes)
                                        .into_iter()
                                        .map(move |mut npc| {
                                            if np {
                                                npc.add_nice_pair(in_out[0], in_out[1])
                                            }

                                            let mut new_path = p.clone();
                                            new_path.nodes[idx] = SuperNode::Zoomed(ZoomedNode {
                                                comp: abs.get_comp().clone(),
                                                npc,
                                                in_node: Some(in_out[0]),
                                                out_node: Some(in_out[1]),
                                                used: abs.used,
                                            });
                                            new_path
                                        })
                                        .collect_vec()
                                })
                                .collect_vec()
                        }
                    } else if let SuperNode::Zoomed(zoomed) = node {
                        if (zoomed.in_node.is_none() || zoomed.out_node.is_none())
                            && idx < path_len - 1
                            && idx > 0
                        {
                            let zoomed_comp = zoomed.get_comp();
                            let np = zoomed_comp.is_c3()
                                || zoomed_comp.is_c4()
                                || (zoomed_comp.is_c5() && !zoomed.used)
                                || zoomed_comp.is_complex();

                            zoomed
                                .get_comp()
                                .nodes()
                                .into_iter()
                                .filter(|node| *node != zoomed.in_node.or(zoomed.out_node).unwrap())
                                .flat_map(|node| {
                                    let in_node = zoomed.in_node.or(Some(node));
                                    let out_node = zoomed.out_node.or(Some(node));

                                    edge_hit_nodes
                                        .iter()
                                        .powerset()
                                        .map(|np_with_node| {
                                            let mut npc = if np {
                                                NicePairConfig {
                                                    nice_pairs: vec![(
                                                        in_node.unwrap(),
                                                        out_node.unwrap(),
                                                    )],
                                                }
                                            } else {
                                                NicePairConfig::empty()
                                            };

                                            for &n in np_with_node {
                                                npc.add_nice_pair(node, n);
                                            }
                                            for &n in &edge_hit_nodes {
                                                if zoomed.get_comp().is_adjacent(n, node) {
                                                    npc.add_nice_pair(node, n);
                                                }
                                            }

                                            let mut new_path = p.clone();
                                            new_path.nodes[idx] = SuperNode::Zoomed(ZoomedNode {
                                                comp: zoomed_comp.clone(),
                                                npc: zoomed.npc.clone().merge(npc),
                                                in_node,
                                                out_node,
                                                used: zoomed.used,
                                            });
                                            new_path
                                        })
                                        .collect_vec()
                                })
                                .collect_vec()
                        } else {
                            vec![p.clone()]
                        }
                    } else {
                        vec![p.clone()]
                    }
                })
                .collect_vec();
        });

        let mut new_instances = paths
            .into_iter()
            .map(|path| AugmentedPathInstance {
                path,
                non_path_matching_edges: vec![],
                fixed_edge: fixed_edges.clone(),
            })
            .collect_vec();

        self.input
            .non_path_matching_edges
            .iter()
            .for_each(|m_edge| {
                new_instances = new_instances
                    .iter()
                    .flat_map(|instance| {
                        let path = &instance.path;
                        let hit = m_edge.hits_path().unwrap();
                        let hit_comp = path.nodes[hit].get_zoomed();

                        let mut nodes = hit_comp
                            .get_comp()
                            .nodes()
                            .iter()
                            .filter(|&n| fixed_edges.iter().any(|e| *n == e.0 || *n == e.1))
                            .cloned()
                            .collect_vec();

                        if let Some(in_node) = hit_comp.in_node {
                            nodes.push(in_node)
                        }
                        if let Some(out_node) = hit_comp.out_node {
                            nodes.push(out_node)
                        }
                        nodes.sort();
                        nodes.dedup();

                        hit_comp
                            .get_comp()
                            .nodes()
                            .into_iter()
                            .flat_map(|hit_node| {
                                nodes
                                    .iter()
                                    .powerset()
                                    .map(|np_with_node| {
                                        let mut new_path = path.clone();
                                        let npc = &mut new_path
                                            .nodes
                                            .get_mut(hit)
                                            .unwrap()
                                            .get_zoomed_mut()
                                            .npc;
                                        for &n in np_with_node {
                                            npc.add_nice_pair(hit_node, n);
                                        }

                                        let mut new_instance = instance.clone();
                                        new_instance.path = new_path;
                                        new_instance
                                            .fixed_edge
                                            .push(Edge(hit_node, m_edge.source()));
                                        new_instance
                                    })
                                    .collect_vec()
                            })
                            .collect_vec()
                    })
                    .collect_vec()
            });

        Box::new(new_instances.into_iter())
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance> for CycleExpanderEnumTactic {
    type Enumer<'a> = CycleExpanderEnumerator<'a>;

    fn msg(&self, data: &AugmentedPathInstance) -> String {
        todo!()
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        todo!()
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        todo!()
    }
}
