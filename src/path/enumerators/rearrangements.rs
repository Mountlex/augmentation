use itertools::Itertools;

use crate::{
    path::{
        extension::{Extension, InOutNode},
        instance::Instance,
        pseudo_cycle::CycleComp,
    },
    Node,
};

// checked

pub fn enumerate_rearrangements(
    instance: &Instance,
    finite: bool,
) -> Box<dyn Iterator<Item = Extension>> {
    let pc = instance.pseudo_cycle().unwrap();

    // A pseudo cycle can only be interpreted as a rearrangement if it only consist of path components and contain all components of the prefix of the nice path
    if !pc.consecutive_end() || pc.cycle.iter().any(|(_, n, _)| n.is_rem()) {
        return Box::new(std::iter::empty());
    }

    if !finite {
        // find path index of newest node in cycle
        // We know by the precondition that all previous nodes in the path are also in this cycle
        // [ ... -- max_idx -- ... ]
        //   --------------    ----
        //     cycle nodes     remaining path node
        let (max_idx, _) = pc
            .cycle
            .iter()
            .enumerate()
            .max_by_key(|(_, (_, comp, _))| comp)
            .unwrap();

        // [<max_idx>,<max_idx + 1>....,new_last]
        let path1 = vec![pc.cycle.split_at(max_idx).1, pc.cycle.split_at(max_idx).0].concat();
        let extension1 = Extension {
            start: path1[0].1.to_idx(),
            start_out: path1[0].2,
            end: path1.last().unwrap().1.to_idx(),
            end_in: path1.last().unwrap().0,
            inner: path1
                .iter()
                .skip(1)
                .take(path1.len() - 2)
                .map(|(n1, c, n2)| InOutNode {
                    in_node: *n1,
                    idx: c.to_idx(),
                    out_node: *n2,
                })
                .collect_vec(),
        };

        // path2 = [<max_idx>,<max_idx - 1>....,new_last]
        let mut p1 = pc.cycle.split_at(max_idx + 1).0.to_vec();
        let mut p2 = pc.cycle.split_at(max_idx + 1).1.to_vec();
        p1.reverse();
        p2.reverse();
        let mut path2 = vec![p1, p2].concat();
        fix_in_out_direction(&mut path2);
        let extension2 = Extension {
            start: path2[0].1.to_idx(),
            start_out: path2[0].2,
            end: path2.last().unwrap().1.to_idx(),
            end_in: path2.last().unwrap().0,
            inner: path2
                .iter()
                .skip(1)
                .take(path2.len() - 2)
                .map(|(n1, c, n2)| InOutNode {
                    in_node: *n1,
                    idx: c.to_idx(),
                    out_node: *n2,
                })
                .collect_vec(),
        };
        // extension:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in]  3 is new last of nice path
        let iter = vec![extension1, extension2].into_iter();

        Box::new(iter)
    } else {
        let len = pc.cycle.len();
        let pc = pc.clone();

        // every comp of pc could be the begin!
        let iter = (0..len).flat_map(move |max_idx| {
            // [<max_idx>,<max_idx + 1>....,new_last]
            let path1 = vec![pc.cycle.split_at(max_idx).1, pc.cycle.split_at(max_idx).0].concat();
            let extension1 = Extension {
                start: path1[0].1.to_idx(),
                start_out: path1[0].2,
                end: path1.last().unwrap().1.to_idx(),
                end_in: path1.last().unwrap().0,
                inner: path1
                    .iter()
                    .skip(1)
                    .take(path1.len() - 2)
                    .map(|(n1, c, n2)| InOutNode {
                        in_node: *n1,
                        idx: c.to_idx(),
                        out_node: *n2,
                    })
                    .collect_vec(),
            };

            // path2 = [<max_idx>,<max_idx - 1>....,new_last]
            let mut p1 = pc.cycle.split_at(max_idx + 1).0.to_vec();
            let mut p2 = pc.cycle.split_at(max_idx + 1).1.to_vec();
            p1.reverse();
            p2.reverse();
            let mut path2 = vec![p1, p2].concat();
            fix_in_out_direction(&mut path2);
            let extension2 = Extension {
                start: path2[0].1.to_idx(),
                start_out: path2[0].2,
                end: path2.last().unwrap().1.to_idx(),
                end_in: path2.last().unwrap().0,
                inner: path2
                    .iter()
                    .skip(1)
                    .take(path2.len() - 2)
                    .map(|(n1, c, n2)| InOutNode {
                        in_node: *n1,
                        idx: c.to_idx(),
                        out_node: *n2,
                    })
                    .collect_vec(),
            };
            // extension:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in]  3 is new last of nice path
            let iter = vec![extension1, extension2].into_iter();
            Box::new(iter)
        });

        Box::new(iter)
    }
}

pub fn fix_in_out_direction(extension: &mut Vec<(Node, CycleComp, Node)>) {
    extension.iter_mut().for_each(|(n1, _c, n2)| {
        std::mem::swap(&mut (*n1), &mut (*n2));
    });
}
