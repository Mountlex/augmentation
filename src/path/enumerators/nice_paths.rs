use crate::{
    comps::{merge_components_to_base, Component, Graph},
    path::{proof::Enumerator, AbstractNode, NicePath, SuperNode},
};

use super::matching_hits::MatchingHitEnumeratorInput;

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
    pub nice_path: NicePath,
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
