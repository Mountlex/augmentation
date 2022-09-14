use itertools::Itertools;

use crate::{
    comps::{Component, Node},
    path::{
        proof::{Enumerator, ProofContext},
        NicePairConfig, PathMatchingInstance, SelectedMatchingInstance, SuperNode, ZoomedNode,
    },
};

pub struct NPCEnumerator;

impl Enumerator<PathMatchingInstance, PathMatchingInstance> for NPCEnumerator {
    fn msg(&self, data_in: &PathMatchingInstance) -> String {
        format!(
            "Enumerate all nice pairs for nodes {:?} of last component",
            data_in.matching.sources()
        )
    }

    fn iter(
        &mut self,
        data_in: PathMatchingInstance,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = PathMatchingInstance>> {
        let super_node = &data_in.path.nodes.last().unwrap();

        assert!(matches!(super_node, crate::path::SuperNode::Abstract(_)));

        let comp = super_node.get_comp().clone();
        let iterator = comp_npcs(&comp, &data_in.matching.sources())
            .into_iter()
            .map(move |npc| {
                let mut path_clone = data_in.path.clone();
                let zoomed_node = ZoomedNode {
                    comp: comp.clone(),
                    npc,
                    in_node: data_in.matching.path_edge_left.map(|e| e.source()),
                    out_node: data_in.matching.path_edge_right.map(|e| e.source()),
                };

                *path_clone.nodes.last_mut().unwrap() = SuperNode::Zoomed(zoomed_node);
                PathMatchingInstance {
                    path: path_clone,
                    matching: data_in.matching.clone(),
                }
            });

        Box::new(iterator)
    }

    fn item_msg(&self, item: &PathMatchingInstance) -> String {
        format!("NPC {}", item.path.nodes.last().unwrap())
    }
}

impl Enumerator<SelectedMatchingInstance, SelectedMatchingInstance> for NPCEnumerator {
    fn msg(&self, data_in: &SelectedMatchingInstance) -> String {
        format!(
            "Enumerate all nice pairs for nodes {:?} of path[{}]",
            data_in.matched, data_in.hit_comp_idx
        )
    }

    fn iter(
        &mut self,
        data_in: SelectedMatchingInstance,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedMatchingInstance>> {
        let super_node = &data_in.path_matching.path.nodes[data_in.hit_comp_idx];

        assert!(matches!(super_node, crate::path::SuperNode::Abstract(_)));

        let comp = super_node.get_comp().clone();
        let iterator = comp_npcs(&comp, &data_in.matched.iter().map(|e| e.0).collect_vec())
            .into_iter()
            .map(move |npc| {
                let mut instance = data_in.path_matching.clone();
                let zoomed_node = ZoomedNode {
                    comp: comp.clone(),
                    npc,
                    in_node: None,
                    out_node: None,
                };

                instance.path.nodes[data_in.hit_comp_idx] = SuperNode::Zoomed(zoomed_node);
                SelectedMatchingInstance {
                    path_matching: instance,
                    matched: data_in.matched.clone(),
                    hit_comp_idx: data_in.hit_comp_idx,
                }
            });

        Box::new(iterator)
    }

    fn item_msg(&self, item: &SelectedMatchingInstance) -> String {
        format!(
            "NPC {}",
            item.path_matching.path.nodes[item.hit_comp_idx]
                .to_zoomed()
                .npc
        )
    }
}

fn comp_npcs(comp: &Component, nodes: &Vec<Node>) -> Vec<NicePairConfig> {
    match comp {
        Component::Cycle(c) if c.edge_count() <= 5 => {
            let all_pairs = nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .collect_vec();
            let adj_pairs: Vec<(u32, u32)> = all_pairs
                .iter()
                .filter(|(u, v)| comp.is_adjacent(*u, *v))
                .cloned()
                .collect();
            all_pairs
                .into_iter()
                .powerset()
                .filter(|config| {
                    // if config misses a nice pair although it is a pair of adjacent vertices, remove it
                    adj_pairs
                        .iter()
                        .all(|(u, v)| config.contains(&(*u, *v)) || config.contains(&(*v, *u)))
                })
                .map(|config| NicePairConfig { nice_pairs: config })
                .collect_vec()
        }
        Component::Cycle(c) => vec![NicePairConfig {
            nice_pairs: c.all_edges().map(|(u, v, _)| (u, v)).collect_vec(),
        }],
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
