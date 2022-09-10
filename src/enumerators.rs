use std::marker::PhantomData;

use itertools::Itertools;
use petgraph::data;

use crate::{
    comps::{merge_components_to_base, Component, Graph, Node},
    nice_path::{
        comp_npcs, AbstractNode, Enumerator, NicePairConfig, NicePath, PathMatchingEdge,
        PathMatchingHits, SuperNode, ZoomedNode, ThreeMatching,
    },
};

pub struct PathEnumeratorInput {
    comps: Vec<Component>,
    last_comp: Component,
}

impl PathEnumeratorInput {
    pub fn new(last_comp: Component, comps: Vec<Component>) -> Self {
        PathEnumeratorInput { comps, last_comp }
    }
}

pub struct PathEnumerator;

pub struct PathEnumeratorOutput {
    nice_path: NicePath,
}

impl Enumerator for PathEnumerator {
    type In = PathEnumeratorInput;

    type Out = PathEnumeratorOutput;

    fn msg(&self, data_in: &Self::In) -> String {
        format!("Enumerate all nice paths ending with {}", data_in.last_comp)
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let comps = &data_in.comps;
        let iter = itertools::iproduct!(comps.clone(), comps.clone(), comps.clone()).map(
            move |(c1, c2, c3)| {
                let path = vec![c1, c2, c3, data_in.last_comp.clone()];
                let (path_graph, path) = merge_components_to_base(Graph::new(), path);

                let nodes = path
                    .into_iter()
                    .map(|c| -> SuperNode {
                        let nice_pair = match &c {
                            Component::Cycle(cycle) if cycle.edge_count() <= 5 => true,
                            Component::Complex(_, _, _) => true,
                            _ => false,
                        };
                        SuperNode::Abstract(AbstractNode {
                            comp: c,
                            nice_pair,
                            used: false,
                        })
                    })
                    .collect();

                let nice_path = NicePath {
                    nodes,
                    graph: path_graph,
                };

                PathEnumeratorOutput { nice_path }
            },
        );

        Box::new(iter)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!("Nice path {}", item.nice_path)
    }
}

impl From<PathEnumeratorOutput> for MatchingHitEnumeratorInput {
    fn from(o: PathEnumeratorOutput) -> Self {
        MatchingHitEnumeratorInput {
            nice_path: o.nice_path,
        }
    }
}

pub struct MatchingHitEnumeratorInput {
    nice_path: NicePath,
}

pub struct MatchingHitEnumerator;

#[derive(Clone)]
pub struct MatchingHitEnumeratorOutput {
    pub nice_path: NicePath,
    pub three_matching: ThreeMatching,
}

impl Enumerator for MatchingHitEnumerator {
    type In = MatchingHitEnumeratorInput;

    type Out = MatchingHitEnumeratorOutput;

    fn msg(&self, _data_in: &Self::In) -> String {
        format!("Enumerate all matching hits from last component")
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let path_len = data_in.nice_path.nodes.len();
        let last_comp = data_in.nice_path.nodes.last().unwrap().get_comp();
        let nodes = last_comp.graph().nodes().collect_vec();

        let mut targets = vec![PathMatchingHits::Outside];
        for i in 0..path_len - 1 {
            targets.push(PathMatchingHits::Path(i));
        }

        let path = data_in.nice_path.clone();

        let iter = nodes
            .into_iter()
            .permutations(3)
            .flat_map(move |m_endpoints| {
                let path_clone = path.clone();
                targets
                    .clone()
                    .into_iter()
                    .combinations_with_replacement(2)
                    .map(move |hits| {
                        let m_path =
                            PathMatchingEdge(m_endpoints[0], PathMatchingHits::Path(path_len - 2));
                        let m1 = PathMatchingEdge(m_endpoints[1], hits[0]);
                        let m2 = PathMatchingEdge(m_endpoints[2], hits[1]);
                        let m = ThreeMatching(m_path, m1, m2);

                        MatchingHitEnumeratorOutput {
                            nice_path: path_clone.clone(),
                            three_matching: m
                        }
                    })
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!("Matching [({}), ({}), ({})]", item.three_matching.0, item.three_matching.1, item.three_matching.2)
    }
}

impl From<MatchingHitEnumeratorOutput> for NPCEnumInput<MatchingHitEnumeratorOutput> {
    fn from(output: MatchingHitEnumeratorOutput) -> Self {
        NPCEnumInput {
            nodes: output.three_matching.sources(),
            comp: output.nice_path.nodes.last().unwrap().get_comp().to_owned(),
            input: output,
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

#[derive(Clone)]
pub struct ComponentHitInput {
    pub nice_path: NicePath,
    pub three_matching: ThreeMatching,
    pub npc_last: NicePairConfig,
}

pub struct ComponentHitEnumerator;

impl Enumerator for ComponentHitEnumerator {
    type In = ComponentHitInput;

    type Out = ComponentHitOutput;

    fn msg(&self, data_in: &Self::In) -> String {
        format!("Enumerate all components hit by matching edges")
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let mut matching = data_in.three_matching.to_vec();
        matching.sort_by_key(|m| m.hit());

        let iter = matching
            .clone()
            .into_iter()
            .filter(|m_edge| m_edge.hits_path().is_some())
            .map(|m_edge| m_edge.hit())
            .dedup_with_count()
            .flat_map(move |(num_edges, hit_comp)| {
                if let PathMatchingHits::Path(hit_comp_idx) = hit_comp {
                    let right_matched: Vec<Node> = matching
                        .iter()
                        .filter(|m_edge| m_edge.hit() == hit_comp)
                        .map(|m_edge| m_edge.source())
                        .collect();
                    assert_eq!(right_matched.len(), num_edges);

                    Some(ComponentHitOutput {
                        path: data_in.nice_path.clone(),
                        npc_last: data_in.npc_last.clone(),
                        three_matching: data_in.three_matching.clone(),
                        hit_comp_idx,
                        right_matched,
                    })
                } else {
                    None
                }
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!("Path[{}] hit by {} matching edges", item.hit_comp_idx, item.right_matched.len())
    }
}

#[derive(Clone)]
pub struct ComponentHitOutput {
    pub path: NicePath,
    pub npc_last: NicePairConfig,
    pub three_matching: ThreeMatching,
    pub hit_comp_idx: usize,
    pub right_matched: Vec<Node>,
}

impl From<ComponentHitOutput> for MatchingNodesEnumeratorInput {
    fn from(o: ComponentHitOutput) -> Self {
        MatchingNodesEnumeratorInput {
            three_matching: o.three_matching,
            right_matched: o.right_matched,
            last_comp: o.path.nodes.last().unwrap().get_comp().clone(),
            left_comp: o.path.nodes[o.hit_comp_idx].get_comp().clone(),
            npc_last: o.npc_last,
        }
    }
}

#[derive(Clone)]
pub struct MatchingNodesEnumeratorInput {
    pub right_matched: Vec<Node>,
    pub three_matching: ThreeMatching,
    pub last_comp: Component,
    pub left_comp: Component,
    pub npc_last: NicePairConfig,
}

pub struct MatchingNodesEnumerator;

impl Enumerator for MatchingNodesEnumerator {
    type In = MatchingNodesEnumeratorInput;

    type Out = MatchingNodesEnumeratorOutput;

    fn msg(&self, data_in: &Self::In) -> String {
        format!("Enumerate matching endpoints at {}", data_in.left_comp)
    }

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>> {
        let iter = data_in
            .left_comp
            .matching_permutations(data_in.right_matched.len())
            .into_iter()
            .map(move |left_matched| MatchingNodesEnumeratorOutput {
                three_matching: data_in.three_matching.clone(),
                left_matched,
                right_matched: data_in.right_matched.clone(),
                last_comp: data_in.last_comp.clone(),
                left_comp: data_in.left_comp.clone(),
                npc_last: data_in.npc_last.clone(),
            });

        Box::new(iter)
    }

    fn item_msg(&self, item: &Self::Out) -> String {
        format!("Matching endpoints {:?}", item.left_matched)
    }
}

#[derive(Clone)]
pub struct MatchingNodesEnumeratorOutput {
    pub three_matching: ThreeMatching,
    pub left_matched: Vec<Node>,
    pub right_matched: Vec<Node>,
    pub last_comp: Component,
    pub left_comp: Component,
    pub npc_last: NicePairConfig,
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
