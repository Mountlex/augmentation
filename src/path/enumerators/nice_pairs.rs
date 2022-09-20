use itertools::Itertools;

use crate::{
    comps::{Component, Node},
    path::{
        proof::{Enumerator, EnumeratorTactic, ProofContext},
        NicePairConfig, PathMatchingInstance, SelectedMatchingInstance, SuperNode, ZoomedNode,
    },
};

pub struct NPCEnumTactic;

pub struct NPCEnumerator<'a, I> {
    instance: &'a I,
}

impl<'a> Enumerator<PathMatchingInstance, PathMatchingInstance>
    for NPCEnumerator<'a, PathMatchingInstance>
{
    fn iter(
        &mut self,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = PathMatchingInstance> + '_> {
        let super_node = &self.instance.path.nodes.last().unwrap().to_abstract();
        let used = super_node.used;

        let comp = super_node.get_comp().clone();
        let iterator = comp_npcs(&comp, &self.instance.matching.sources())
            .into_iter()
            .map(move |npc| {
                let mut path_clone = self.instance.path.clone();
                let zoomed_node = ZoomedNode {
                    comp: comp.clone(),
                    npc,
                    in_node: self.instance.matching.path_edge_left.map(|e| e.source()),
                    out_node: self.instance.matching.path_edge_right.map(|e| e.source()),
                    used,
                };

                *path_clone.nodes.last_mut().unwrap() = SuperNode::Zoomed(zoomed_node);
                PathMatchingInstance {
                    path: path_clone,
                    matching: self.instance.matching.clone(),
                }
            });

        Box::new(iterator)
    }
}

impl<'a> Enumerator<SelectedMatchingInstance, SelectedMatchingInstance>
    for NPCEnumerator<'a, SelectedMatchingInstance>
{
    fn iter(
        &mut self,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = SelectedMatchingInstance> + '_> {
        let super_node =
            &self.instance.path_matching.path.nodes[self.instance.hit_comp_idx].to_abstract();
        let used = super_node.used;

        let comp = super_node.get_comp().clone();
        let iterator = comp_npcs(
            &comp,
            &self.instance.matched.iter().map(|e| e.0).collect_vec(),
        )
        .into_iter()
        .map(move |npc| {
            let mut instance = self.instance.path_matching.clone();
            let zoomed_node = ZoomedNode {
                comp: comp.clone(),
                npc,
                in_node: None,
                out_node: None,
                used,
            };

            instance.path.nodes[self.instance.hit_comp_idx] = SuperNode::Zoomed(zoomed_node);
            SelectedMatchingInstance {
                path_matching: instance,
                matched: self.instance.matched.clone(),
                hit_comp_idx: self.instance.hit_comp_idx,
            }
        });

        Box::new(iterator)
    }
}

impl EnumeratorTactic<PathMatchingInstance, PathMatchingInstance> for NPCEnumTactic {
    type Enumer<'a> = NPCEnumerator<'a, PathMatchingInstance>;

    fn msg(&self, data_in: &PathMatchingInstance) -> String {
        format!(
            "Enumerate all nice pairs for nodes {:?} of last component",
            data_in.matching.sources()
        )
    }

    fn item_msg(&self, item: &PathMatchingInstance) -> String {
        format!("NPC {}", item.path.nodes.last().unwrap())
    }

    fn get_enumerator<'a>(&'a self, data: &'a PathMatchingInstance) -> Self::Enumer<'a> {
        NPCEnumerator { instance: data }
    }
}

impl EnumeratorTactic<SelectedMatchingInstance, SelectedMatchingInstance> for NPCEnumTactic {
    type Enumer<'a> = NPCEnumerator<'a, SelectedMatchingInstance>;

    fn msg(&self, data_in: &SelectedMatchingInstance) -> String {
        format!(
            "Enumerate all nice pairs for nodes {:?} of path[{}]",
            data_in.matched, data_in.hit_comp_idx
        )
    }

    fn item_msg(&self, item: &SelectedMatchingInstance) -> String {
        format!(
            "NPC {}",
            item.path_matching.path.nodes[item.hit_comp_idx]
                .to_zoomed()
                .npc
        )
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedMatchingInstance) -> Self::Enumer<'a> {
        NPCEnumerator { instance: data }
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
