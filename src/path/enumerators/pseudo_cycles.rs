use itertools::{iproduct, Itertools};

use crate::{
    path::{proof::Instance, CycleComp, MatchingEdge, PathComp, Pidx, PseudoCycle},
    types::Edge,
    Node,
};

pub fn enumerate_pseudo_cycles(instance: &Instance) -> Box<dyn Iterator<Item = PseudoCycle> + '_> {
    let mut iter: Box<dyn Iterator<Item = PseudoCycle>> = Box::new(std::iter::empty());
    let path_comps = instance.path_nodes().cloned().collect_vec();
    let all_edges = instance.all_edges();
    let mut all_rem_edges = instance.rem_edges().into_iter().collect_vec();
    let last_comp = path_comps.last().unwrap();
    all_rem_edges.push(MatchingEdge {
        source: last_comp.in_node.unwrap(),
        source_idx: last_comp.path_idx,
        matching: true,
    });

    if path_comps.len() < 2 {
        return Box::new(std::iter::empty());
    }

    for i in 3..path_comps.len() + 2 {
        let fixed_edge_iter = pseudo_cycles_of_length(
            path_comps.clone(),
            all_edges.clone(),
            all_rem_edges.clone(),
            i,
        );
        iter = Box::new(iter.chain(fixed_edge_iter))
    }
    iter
}

pub fn product_of_first(
    mut edges: Vec<Vec<(Node, Node)>>,
    length: usize,
) -> Box<dyn Iterator<Item = Vec<(Node, Node)>>> {
    assert_eq!(length, edges.len());
    if length == 7 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);
        let edges5 = edges.remove(0);
        let edges6 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4, edges5, edges6)
                .map(|(e1, e2, e3, e4, e5, e6, e7)| vec![e1, e2, e3, e4, e5, e6, e7]),
        )
    } else if length == 6 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);
        let edges5 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4, edges5)
                .map(|(e1, e2, e3, e4, e5, e6)| vec![e1, e2, e3, e4, e5, e6]),
        )
    } else if length == 5 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4)
                .map(|(e1, e2, e3, e4, e5)| vec![e1, e2, e3, e4, e5]),
        )
    } else if length == 4 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3).map(|(e1, e2, e3, e4)| vec![e1, e2, e3, e4]),
        )
    } else if length == 3 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);

        Box::new(iproduct!(edges0, edges1, edges2).map(|(e1, e2, e3)| vec![e1, e2, e3]))
    } else if length == 2 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);

        Box::new(iproduct!(edges0, edges1).map(|(e1, e2)| vec![e1, e2]))
    } else if length == 1 {
        let edges0 = edges.remove(0);

        Box::new(iproduct!(edges0).map(|e1| vec![e1]))
    } else {
        panic!("Length {} not supported!", length)
    }
}

fn edges_between(
    edges: &[Edge],
    rem_edges: &[MatchingEdge],
    i1: &CycleComp,
    i2: &CycleComp,
) -> Vec<(Node, Node)> {
    match (i1, i2) {
        (CycleComp::PathComp(idx1), CycleComp::PathComp(idx2)) => edges
            .iter()
            .filter(|e| e.between_path_nodes(*idx1, *idx2))
            .map(|e| {
                if e.path_index_n1 == *idx1 {
                    (e.n1, e.n2)
                } else {
                    (e.n2, e.n1)
                }
            })
            .collect_vec(),
        (CycleComp::PathComp(idx), CycleComp::Rem) => rem_edges
            .iter()
            .filter(|e| e.source_idx == *idx)
            .map(|e| (e.source, Node::Rem))
            .collect_vec(),
        (CycleComp::Rem, CycleComp::PathComp(idx)) => rem_edges
            .iter()
            .filter(|e| e.source_idx == *idx)
            .map(|e| (Node::Rem, e.source))
            .collect_vec(),
        (CycleComp::Rem, CycleComp::Rem) => panic!(),
    }
}

fn pseudo_cycles_of_length(
    path_comps: Vec<PathComp>,
    all_edges: Vec<Edge>,
    all_rem_edges: Vec<MatchingEdge>,
    length: usize,
) -> impl Iterator<Item = PseudoCycle> {
    let path_len = path_comps.len();
    Pidx::range(path_len)
        .into_iter()
        .map(|idx| CycleComp::PathComp(idx))
        .chain(std::iter::once(CycleComp::Rem))
        .permutations(length)
        .filter(|perm| perm.iter().min() == perm.first())
        .flat_map(move |perm| {
            let length = length;
            let first = perm[0].clone();
            let cons_edges = vec![perm.clone(), vec![first]]
                .concat()
                .windows(2)
                .map(|e| edges_between(&all_edges, &all_rem_edges, &e[0], &e[1]))
                .collect_vec();

            product_of_first(cons_edges, length).map(move |e| {
                let cycle_indices = &perm;

                assert_eq!(cycle_indices.len(), length);

                let cycle = cycle_indices
                    .into_iter()
                    .enumerate()
                    .map(|(i, cycle_comp)| {
                        let last_edge = if i == 0 { length - 1 } else { i - 1 };
                        (e[last_edge].1, cycle_comp.clone(), e[i].0)
                    })
                    .collect_vec();

                // cycle nodes:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in:3.out -- 0.in]
                PseudoCycle { cycle }
            })
        })
}
