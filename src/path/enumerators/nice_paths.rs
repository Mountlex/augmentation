use crate::{
    comps::{merge_components_to_base, Component, Graph},
    path::{
        proof::{Enumerator, ProofContext},
        AbstractNode, PathInstance, SuperNode,
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

impl Enumerator<PathEnumeratorInput, PathInstance> for PathEnumerator {
    fn msg(&self, data_in: &PathEnumeratorInput) -> String {
        format!("Enumerate all nice paths ending with {}", data_in.last_comp)
    }

    fn iter(
        &self,
        data_in: PathEnumeratorInput,
        _context: &ProofContext,
    ) -> Box<dyn Iterator<Item = PathInstance>> {
        let comps = &data_in.comps;
        let iter = itertools::iproduct!(comps.clone(), comps.clone(), comps.clone()).map(
            move |(c1, c2, c3)| {
                let path = vec![c1, c2, c3, data_in.last_comp.clone()];
                let (_path_graph, path) = merge_components_to_base(Graph::new(), path);

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

                let nice_path = PathInstance { nodes };

                nice_path
            },
        );

        Box::new(iter)
    }

    fn item_msg(&self, item: &PathInstance) -> String {
        format!("Nice path {}", item)
    }
}
