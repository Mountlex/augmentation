use itertools::Itertools;

use crate::{
    path::{proof::Instance, CycleComp, Rearrangement},
    Node,
};

pub fn enumerate_rearrangements(instance: &Instance) -> Box<dyn Iterator<Item = Rearrangement>> {
    let pc = instance.pseudo_cycle().unwrap();

    if !pc.consecutive_end() || pc.cycle.iter().any(|(_, n, _)| n.is_rem()) {
        return Box::new(std::iter::empty());
    }

    // find path index of last node in cycle
    // We know by the precondition that all previous nodes in the path are also in this cycle
    // [...,hit,cycle_nodes]
    let (cycle_idx, path_comp) = pc.cycle.iter().enumerate().max_by_key(|n| n.1).unwrap();

    // [hit,<cycle_idx + 1>....,new_last]
    let path1 = vec![
        pc.cycle.split_at(cycle_idx).1,
        pc.cycle.split_at(cycle_idx).0,
    ]
    .concat();
    let mut extension1 = path1
        .into_iter()
        .map(|(n1, c, n2)| (Some(n1), *c.to_idx(), Some(n2)))
        .collect_vec();
    extension1.last_mut().unwrap().2 = None;

    // [hit,<cycle_idx - 1>....,new_last]
    let mut p1 = pc.cycle.split_at(cycle_idx + 1).0.to_vec();
    let mut p2 = pc.cycle.split_at(cycle_idx + 1).1.to_vec();
    p1.reverse();
    p2.reverse();
    let mut path2 = vec![p1, p2].concat();
    fix_in_out_direction(&mut path2);
    let mut extension2 = path2
        .into_iter()
        .map(|(n1, c, n2)| (Some(n1), *c.to_idx(), Some(n2)))
        .collect_vec();
    extension2.last_mut().unwrap().2 = None;

    // extension:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in]  3 is new last of nice path
    let iter = vec![
        Rearrangement {
            extension: extension1,
        },
        Rearrangement {
            extension: extension2,
        },
    ]
    .into_iter();

    Box::new(iter)
}

pub fn fix_in_out_direction(extension: &mut Vec<(Node, CycleComp, Node)>) {
    extension.iter_mut().for_each(|(n1, c, n2)| {
        let tmp = *n1;
        *n1 = *n2;
        *n2 = tmp;
    });
}
