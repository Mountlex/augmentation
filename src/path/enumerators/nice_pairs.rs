use std::marker::PhantomData;

use itertools::Itertools;

use crate::{
    comps::{Component, Node},
    path::{proof::Enumerator, NicePairConfig},
};

use super::{
    comp_hits::ComponentHitInput, matching_hits::MatchingHitEnumeratorOutput,
    matching_nodes::MatchingNodesEnumeratorOutput,
};

impl From<MatchingHitEnumeratorOutput> for NPCEnumInput<MatchingHitEnumeratorOutput> {
    fn from(output: MatchingHitEnumeratorOutput) -> Self {
        NPCEnumInput {
            nodes: output.three_matching.sources(),
            comp: output.nice_path.nodes.last().unwrap().get_comp().to_owned(),
            input: output,
        }
    }
}

impl From<MatchingNodesEnumeratorOutput> for NPCEnumInput<MatchingNodesEnumeratorOutput> {
    fn from(output: MatchingNodesEnumeratorOutput) -> Self {
        NPCEnumInput {
            input: output.clone(),
            nodes: output.left_matched,
            comp: output.left_comp,
        }
    }
}

#[derive(Clone)]
pub struct NPCEnumInput<I> {
    nodes: Vec<Node>,
    comp: Component,
    input: I,
}

pub struct NPCEnumerator<I> {
    _data: PhantomData<I>,
}

impl<I> NPCEnumerator<I> {
    pub fn new() -> Self {
        NPCEnumerator { _data: PhantomData }
    }
}

impl<I> Enumerator for NPCEnumerator<I>
where
    I: Clone + 'static,
{
    type In = NPCEnumInput<I>;

    type Out = NPCEnumOutput<I>;

    fn msg(&self, data_in: &Self::In) -> String {
        format!(
            "Enumerate all nice pairs for nodes {:?} of component {}",
            data_in.nodes, data_in.comp
        )
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let iterator = comp_npcs(&data_in.comp, &data_in.nodes)
            .into_iter()
            .map(move |npc| NPCEnumOutput {
                input: data_in.input.clone(),
                npc,
            });

        Box::new(iterator)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!("Nice pair configuration {}", item.npc)
    }
}

#[derive(Clone)]
pub struct NPCEnumOutput<I> {
    pub input: I,
    pub npc: NicePairConfig,
}

impl From<NPCEnumOutput<MatchingHitEnumeratorOutput>> for ComponentHitInput {
    fn from(o: NPCEnumOutput<MatchingHitEnumeratorOutput>) -> Self {
        ComponentHitInput {
            nice_path: o.input.nice_path,
            three_matching: o.input.three_matching,
            npc_last: o.npc,
        }
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
            nice_pairs: c.all_edges().map(|(u, v, t)| (u, v)).collect_vec(),
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
