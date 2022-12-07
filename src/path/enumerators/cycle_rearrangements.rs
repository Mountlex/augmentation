use crate::{
    path::{proof::PathContext, PathRearrangementInstance, PseudoCycleInstance, SuperNode},
    proof_logic::{Enumerator, EnumeratorTactic},
};

#[derive(Clone)]
pub struct PathRearrangementEnum;

pub struct PathRearrangementEnumerator<'a> {
    input: &'a PseudoCycleInstance,
}

impl<'a> Enumerator<PathRearrangementInstance, PathContext> for PathRearrangementEnumerator<'a> {
    fn iter(
        &self,
        _context: &PathContext,
    ) -> Box<dyn Iterator<Item = PathRearrangementInstance> + '_> {
        let instance = self.input;

        // find path index of last node in cycle
        // We know by the precondition that all previous nodes in the path are also in this cycle
        // [...,hit,cycle_nodes]
        let (cycle_idx, node) = instance
            .pseudo_cycle
            .nodes
            .iter()
            .enumerate()
            .max_by_key(|(_, n)| n.path_idx())
            .unwrap();

        // [hit,<cycle_idx + 1>....,new_last]
        let path1 = vec![
            instance.pseudo_cycle.nodes.split_at(cycle_idx).1,
            instance.pseudo_cycle.nodes.split_at(cycle_idx).0,
        ]
        .concat();

        // [hit,<cycle_idx - 1>....,new_last]
        let mut p1 = instance
            .pseudo_cycle
            .nodes
            .split_at(cycle_idx + 1)
            .0
            .to_vec();
        let mut p2 = instance
            .pseudo_cycle
            .nodes
            .split_at(cycle_idx + 1)
            .1
            .to_vec();
        p1.reverse();
        p2.reverse();
        let mut path2 = vec![p1, p2].concat();
        fix_in_out_direction(&mut path2);

        // extension:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in]  3 is new last of nice path
        let iter = vec![
            PathRearrangementInstance {
                instance: self.input.instance.clone(),
                start_idx: node.path_idx(),
                extension: path1,
            },
            PathRearrangementInstance {
                instance: self.input.instance.clone(),
                start_idx: node.path_idx(),
                extension: path2,
            },
        ]
        .into_iter();

        Box::new(iter)
    }
}

fn fix_in_out_direction(extension: &mut Vec<SuperNode>) {
    extension.iter_mut().for_each(|node| {
        if let SuperNode::Zoomed(node) = node {
            let temp = node.in_node;
            node.in_node = node.out_node;
            node.out_node = temp;
        }
    });
}

impl EnumeratorTactic<PseudoCycleInstance, PathRearrangementInstance, PathContext>
    for PathRearrangementEnum
{
    type Enumer<'a> = PathRearrangementEnumerator<'a>;

    fn msg(&self, _data_in: &PseudoCycleInstance) -> String {
        format!("PseudoCycle on prefix. Consider rearrangements.")
    }

    fn get_enumerator<'a>(&'a self, data: &'a PseudoCycleInstance) -> Self::Enumer<'a> {
        PathRearrangementEnumerator { input: data }
    }

    fn item_msg(&self, item: &PathRearrangementInstance) -> String {
        format!("Path rearrangement starting at {}", item.start_idx)
    }

    fn precondition(&self, data: &PseudoCycleInstance, _context: &PathContext) -> bool {
        data.pseudo_cycle.consecutive_end() && !data.pseudo_cycle.nodes.iter().any(|n| matches!(n, SuperNode::RemPath(_)))
    }
}
