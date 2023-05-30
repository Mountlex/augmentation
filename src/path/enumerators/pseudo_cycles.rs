use itertools::Itertools;

use crate::{
    path::{
        instance::Instance,
        pseudo_cycle::{CycleComp, PseudoCycle},
        EdgeId, HalfAbstractEdge, PathComp, 
    },
    util::product_of_first,
    types::Edge,
    Credit, Node,
};

pub fn enumerate_pseudo_cycles(
    instance: &Instance,
    finite: bool,
) -> Box<dyn Iterator<Item = PseudoCycle>> {
    let path_comps = instance.path_nodes().cloned().collect_vec();
    let all_edges = instance.all_edges();
    //let last_single_edge = instance.last_single_edge();
    let mut all_rem_edges = instance.rem_edges();
    let last_comp = path_comps.last().cloned().unwrap();
    all_rem_edges.push(HalfAbstractEdge {
        source: last_comp.in_node.unwrap(),
        source_idx: last_comp.path_idx,
        cost: Credit::from_integer(1),
        id: EdgeId(0),
    });

    if path_comps.len() < 3 {
        return Box::new(std::iter::empty());
    }

    let mut iter: Box<dyn Iterator<Item = PseudoCycle>> = Box::new(std::iter::empty());
    for i in 3..=(path_comps.len() + 1) {
        let fixed_edge_iter = pseudo_cycles_of_length(
            path_comps.clone(),
            None,
            all_edges.clone(),
            all_rem_edges.clone(),
            i,
            !finite,
        );
        iter = Box::new(iter.chain(fixed_edge_iter))
    }
    iter
}


pub fn edges_between(
    edges: &[Edge],
    last_single_edge: Option<Edge>,
    rem_edges: &[HalfAbstractEdge],
    i1: &CycleComp,
    i2: &CycleComp,
) -> Vec<((Node, Node), Credit)> {
    match (i1, i2) {
        (CycleComp::PathComp(idx1), CycleComp::PathComp(idx2)) => {
            if let Some(edge) = last_single_edge {
                if edge.between_path_nodes(*idx1, *idx2) {
                    return vec![(edge.nodes_between_path_nodes(*idx1, *idx2), edge.cost)];
                }
            }
            return edges
                .iter()
                .filter(|e| e.between_path_nodes(*idx1, *idx2))
                .map(|e| (e.nodes_between_path_nodes(*idx1, *idx2), e.cost))
                .collect_vec();
        }
        (CycleComp::PathComp(idx), CycleComp::Rem) => rem_edges
            .iter()
            .filter(|e| e.source_idx == *idx)
            .map(|e| ((e.source, Node::Rem), e.cost))
            .collect_vec(),
        (CycleComp::Rem, CycleComp::PathComp(idx)) => rem_edges
            .iter()
            .filter(|e| e.source_idx == *idx)
            .map(|e| ((Node::Rem, e.source), e.cost))
            .collect_vec(),
        (CycleComp::Rem, CycleComp::Rem) => panic!(),
    }
}

pub fn pseudo_cycles_of_length(
    path_comps: Vec<PathComp>,
    last_single_edge: Option<Edge>,
    all_edges: Vec<Edge>,
    all_rem_edges: Vec<HalfAbstractEdge>,
    length: usize,
    with_rem: bool,
) -> impl Iterator<Item = PseudoCycle> {
    let indices = path_comps.iter().map(|c| c.path_idx).collect_vec();

    let comps = if with_rem {
        indices
            .into_iter()
            .map(CycleComp::PathComp)
            .chain(std::iter::once(CycleComp::Rem))
            .collect_vec()
    } else {
        indices.into_iter().map(CycleComp::PathComp).collect_vec()
    };

    comps
        .into_iter()
        .permutations(length)
        .filter(|perm| perm.iter().min() == perm.first())
        .flat_map(move |perm| {
            let length = length;
            let first = perm[0].clone();
            let cons_edges = vec![perm.clone(), vec![first]]
                .concat()
                .windows(2)
                .map(|e| edges_between(&all_edges, last_single_edge, &all_rem_edges, &e[0], &e[1]))
                .collect_vec();

            assert_eq!(length, cons_edges.len());

            product_of_first(cons_edges).flat_map(move |edges| {
                let cycle_indices = &perm;

                // at most one credit gaining edge
                if edges
                    .iter()
                    .filter(|(_, c)| *c < Credit::from_integer(1))
                    .count()
                    <= 1
                {
                    let total_edge_cost = edges.iter().map(|(_, c)| *c).sum();

                    assert_eq!(cycle_indices.len(), length);

                    let cycle = cycle_indices
                        .iter()
                        .enumerate()
                        .map(|(i, cycle_comp)| {
                            let last_edge = if i == 0 { length - 1 } else { i - 1 };
                            (edges[last_edge].0 .1, cycle_comp.clone(), edges[i].0 .0)
                        })
                        .collect_vec();

                    // cycle nodes:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in:3.out -- 0.in]
                    Some(PseudoCycle {
                        cycle,
                        total_edge_cost,
                    })
                } else {
                    None
                }
            })
        })
}
