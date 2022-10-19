use itertools::Itertools;

use crate::{
    comps::CompType,
    path::{
        proof::{PathContext, PathNode},
        AbstractNode, AugmentedPathInstance, Pidx, SuperNode,
    },
    proof_logic::{Enumerator, EnumeratorTactic},
    util::relabels_nodes_sequentially,
};

#[derive(Clone)]
pub struct PathEnumeratorInput {
    comps: Vec<PathNode>,
    last_comp: PathNode,
}

impl PathEnumeratorInput {
    pub fn new(last_comp: PathNode, comps: Vec<PathNode>) -> Self {
        PathEnumeratorInput { comps, last_comp }
    }
}

#[derive(Clone)]
pub struct PathEnum;

pub struct PathEnumerator<'a> {
    input: &'a PathEnumeratorInput,
}

impl<'a> Enumerator<AugmentedPathInstance, PathContext> for PathEnumerator<'a> {
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let comps = &self.input.comps;

        let iter = itertools::iproduct!(comps.clone(), comps.clone()).map(move |(c1, c2)| {
            let path = vec![self.input.last_comp.clone(), c1, c2];

            let mut path_updated = path.iter().map(|n| n.get_comp().clone()).collect_vec();
            relabels_nodes_sequentially(&mut path_updated, 0);

            let path = path
                .into_iter()
                .zip(path_updated.into_iter())
                .map(|(o, n)| match o {
                    PathNode::Used(_) => PathNode::Used(n),
                    PathNode::Unused(_) => PathNode::Unused(n),
                })
                .collect_vec();

            let nodes = path
                .into_iter()
                .enumerate()
                .map(|(i, c)| -> SuperNode {
                    let nice_pair = match c.get_comp().comp_type() {
                        CompType::Cycle(num) if num <= 4 => true,
                        CompType::Cycle(num) if num == 5 && i == 1 && !c.is_used() => true,
                        CompType::Complex => true,
                        _ => false,
                    };

                    let in_not_out = if c.get_comp().is_c5() && i == 1 {
                        true
                    } else {
                        nice_pair
                    };

                    SuperNode::Abstract(AbstractNode {
                        comp: c.get_comp().clone(),
                        nice_pair,
                        used: c.is_used(),
                        in_not_out,
                        path_idx: Pidx::from(i),
                    })
                })
                .collect();

            AugmentedPathInstance {
                nodes,
                abstract_edges: vec![],
                fixed_edges: vec![],
            }
        });

        Box::new(iter)
    }
}

impl EnumeratorTactic<PathEnumeratorInput, AugmentedPathInstance, PathContext> for PathEnum {
    type Enumer<'a> = PathEnumerator<'a>;

    fn msg(&self, data_in: &PathEnumeratorInput) -> String {
        if data_in.last_comp.is_used() {
            format!(
                "Enumerate all nice paths ending with used {}",
                data_in.last_comp.get_comp()
            )
        } else {
            format!(
                "Enumerate all nice paths ending with unused {}",
                data_in.last_comp.get_comp()
            )
        }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!("Nice path {}", item)
    }

    fn get_enumerator<'a>(&'a self, data: &'a PathEnumeratorInput) -> Self::Enumer<'a> {
        PathEnumerator { input: data }
    }
}
