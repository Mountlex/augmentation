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
pub struct IterCompEnum {
    comps: Vec<PathNode>,
}

impl IterCompEnum {
    pub fn new(comps: Vec<PathNode>) -> Self {
        IterCompEnum { comps }
    }
}

pub struct IterCompEnumerator<'a> {
    input: &'a AugmentedPathInstance,
    comps: Vec<PathNode>,
}

impl<'a> Enumerator<AugmentedPathInstance, PathContext> for IterCompEnumerator<'a> {
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = AugmentedPathInstance> + '_> {
        let iter = self.comps.iter().map(|node| {
            let comp = node.get_comp().clone();
            let num_used_labels = self
                .input
                .nodes
                .iter()
                .map(|c| c.get_comp().num_labels())
                .sum::<usize>() as u32;
            let mut new_comps = vec![comp];
            relabels_nodes_sequentially(&mut new_comps, num_used_labels);
            let comp = new_comps.remove(0);

            let new_node = match node {
                PathNode::Used(_) => PathNode::Used(comp),
                PathNode::Unused(_) => PathNode::Unused(comp),
            };

            let mut instance = self.input.clone();

            let nice_pair = match new_node.get_comp().comp_type() {
                CompType::Cycle(num) if num <= 4 => true,
                CompType::Complex => true,
                _ => false,
            };

            let in_not_out = nice_pair;

            let super_node = SuperNode::Abstract(AbstractNode {
                comp: new_node.get_comp().clone(),
                nice_pair,
                used: new_node.is_used(),
                in_not_out,
                path_idx: Pidx::from(instance.path_len()),
            });

            instance.nodes.push(super_node);
            instance
        });
        Box::new(iter)
    }
}

impl EnumeratorTactic<AugmentedPathInstance, AugmentedPathInstance, PathContext> for IterCompEnum {
    type Enumer<'a> = IterCompEnumerator<'a>;

    fn msg(&self, _data_in: &AugmentedPathInstance) -> String {
        String::new()
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        IterCompEnumerator {
            input: data,
            comps: self.comps.clone(),
        }
    }

    fn item_msg(&self, item: &AugmentedPathInstance) -> String {
        format!(
            "Enumerate {}th component {}",
            item.nodes.len(),
            item.nodes.last().unwrap()
        )
    }
}
