use itertools::Itertools;

use crate::comps::Component;
use crate::path::extension::{Extension, InOutNode};
use crate::path::path_definition::valid_in_out_npc;
use crate::path::{instance::InstPart, instance::Instance};
use crate::util::{hamiltonian_paths, product_of_first};
use crate::{
    path::{
        proof::check_progress, tactics::check_fixed_extension_feasible, HalfAbstractEdge, PathComp,
        Pidx,
    },
    types::Edge,
    Credit, Node,
};

pub fn edge_enumerator(
    instance: &mut Instance,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().collect_vec();
    let len = path_comps.len();

    let mut nodes_to_pidx: Vec<Option<Pidx>> = vec![None; len * 20];
    for path_comp in &path_comps {
        for node in path_comp.comp.nodes() {
            nodes_to_pidx[node.get_id() as usize] = Some(path_comp.path_idx);
        }
    }

    let res = greedy_evaluation(
        instance,
        &nodes_to_pidx,
        finite,
        vec![
            Box::new(check_comp_config),
            Box::new(check_gainful_edges),
            Box::new(check_comp_three_matching),
            Box::new(check_three_matching),
            Box::new(check_four_matching),
            Box::new(check_comp_contractability),
        ],
    );

    if let Some((iter, name)) = res {
        let cases = iter.collect_vec();
        let iter = compute_good_edges(instance, finite, Box::new(cases.into_iter()));
        Some((iter, name))
    } else {
        None
    }
}

fn greedy_evaluation(
    instance: &Instance,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    finite: bool,
    funcs: Vec<
        Box<
            dyn Fn(
                &Instance,
                &Vec<Option<Pidx>>,
                bool,
            ) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)>,
        >,
    >,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    for f in funcs {
        let res = f(instance, nodes_to_pidx, finite);
        if res.is_some() {
            return res;
        }
    }

    None
}

fn check_comp_three_matching(
    instance: &Instance,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().collect_vec();
    let len = path_comps.len();
    let iter = if finite {
        path_comps.iter().collect_vec()
    } else {
        path_comps.iter().take(len - 1).collect_vec()
    };
    for path_comp in iter {
        let idx = path_comp.path_idx;
        let comp_nodes = path_comp.comp.nodes().to_vec();

        if let Some(iter) = ensure_three_matching(comp_nodes, instance, finite) {
            let iter = to_cases(iter, nodes_to_pidx, instance, true);
            return Some((iter, format!("3-Matching of {}", idx)));
        }
    }
    None
}

fn check_comp_config(
    instance: &Instance,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    _finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().collect_vec();
    let comp = path_comps.first().unwrap();
    let incident_edges = instance
        .all_edges()
        .into_iter()
        .filter(|e| e.path_incident(comp.path_idx))
        .collect_vec();

    let incident_back_edges = instance
        .rem_edges()
        .into_iter()
        .filter(|e| e.source_idx == comp.path_idx)
        .collect_vec();

    let incident_out_edges = instance
        .out_edges()
        .into_iter()
        .filter(|n| comp.comp.contains(n))
        .collect_vec();

    let complement = path_comps
        .iter()
        .skip(1)
        .flat_map(|p| p.comp.nodes().to_vec())
        .filter(|n| n != &comp.in_node.unwrap())
        .collect_vec();

    if incident_edges.len() == 1 && incident_out_edges.is_empty() && incident_back_edges.is_empty()
    {
        if comp.comp.is_c7() {
            let in_node = comp.in_node.unwrap();
            let nodes = comp.comp.nodes();
            assert!(nodes[0] == in_node);

            let configs = vec![
                vec![nodes[1], nodes[2]],
                vec![nodes[1], nodes[6]],
                vec![nodes[1], nodes[3]],
                vec![nodes[1], nodes[5]],
                vec![nodes[1], nodes[4]],
                vec![nodes[2], nodes[5]],
                vec![nodes[2], nodes[4]],
                vec![nodes[3], nodes[4]],
            ];

            let mut all_cases: Box<dyn Iterator<Item = InstPart>> = Box::new(std::iter::empty());
            for config in configs {
                let edge_iter = full_edge_iterator(config, complement.clone(), false, true, true);
                let iter = to_cases_mul(edge_iter, nodes_to_pidx, instance, true);
                all_cases = Box::new(all_cases.chain(iter));
            }
            return Some((all_cases, "C7 config".into()));
        }

        if comp.comp.is_c6() {
            let in_node = comp.in_node.unwrap();
            let nodes = comp.comp.nodes();
            assert!(nodes[0] == in_node);

            let configs = vec![
                vec![nodes[1], nodes[2]],
                vec![nodes[1], nodes[5]],
                vec![nodes[1], nodes[4]],
                vec![nodes[1], nodes[3]],
                vec![nodes[2], nodes[4]],
            ];

            let mut all_cases: Box<dyn Iterator<Item = InstPart>> = Box::new(std::iter::empty());
            for config in configs {
                let edge_iter = full_edge_iterator(config, complement.clone(), false, true, true); // TODO no outside edges!
                let iter = to_cases_mul(edge_iter, nodes_to_pidx, instance, true);
                all_cases = Box::new(all_cases.chain(iter));
            }
            return Some((all_cases, "C6 config".into()));
        }

        if comp.comp.is_c5() {
            let in_node = comp.in_node.unwrap();
            let nodes = comp.comp.nodes();
            assert!(nodes[0] == in_node);

            let configs = vec![
                vec![nodes[1], nodes[2]],
                vec![nodes[1], nodes[4]],
                vec![nodes[1], nodes[3]],
                vec![nodes[4], nodes[2]],
                //vec![nodes[2], nodes[3]],
            ];

            let mut all_cases: Box<dyn Iterator<Item = InstPart>> = Box::new(std::iter::empty());
            for config in configs {
                let edge_iter = full_edge_iterator(config, complement.clone(), true, true, true);
                let iter = to_cases_mul(edge_iter, nodes_to_pidx, instance, true);
                all_cases = Box::new(all_cases.chain(iter));
            }
            return Some((all_cases, "C5 config".into()));
        }

        if comp.comp.is_c4() {
            let in_node = comp.in_node.unwrap();
            let nodes = comp.comp.nodes();
            assert!(nodes[0] == in_node);

            let configs = vec![vec![nodes[1], nodes[2]], vec![nodes[1], nodes[3]]];

            let mut all_cases: Box<dyn Iterator<Item = InstPart>> = Box::new(std::iter::empty());
            for config in configs {
                let edge_iter = full_edge_iterator(config, complement.clone(), true, true, true);
                let iter = to_cases_mul(edge_iter, nodes_to_pidx, instance, true);
                all_cases = Box::new(all_cases.chain(iter));
            }
            return Some((all_cases, "C4 config".into()));
        }
    }
    None
}

fn check_three_matching(
    instance: &Instance,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().collect_vec();
    let len = path_comps.len();

    if finite {
        let path_comps = instance.path_nodes().collect_vec();

        for left_side in path_comps.into_iter().powerset().filter(|p| p.len() >= 2) {
            let comp_nodes = left_side
                .iter()
                .flat_map(|c| c.comp.nodes().to_vec())
                .collect_vec();

            if let Some(iter) = ensure_three_matching(comp_nodes, instance, finite) {
                let iter = to_cases(iter, nodes_to_pidx, instance, true);
                return Some((iter, "3-Matching of first pathnodes".to_string()));
            }
        }
    } else {
        let path_comps = instance.path_nodes().take(len - 2).collect_vec();

        for left_side in path_comps.into_iter().powerset().filter(|p| p.len() >= 2) {
            let comp_nodes = left_side
                .iter()
                .flat_map(|c| c.comp.nodes().to_vec())
                .collect_vec();

            if let Some(iter) = ensure_three_matching(comp_nodes, instance, finite) {
                let iter = to_cases(iter, nodes_to_pidx, instance, true);
                return Some((iter, "3-Matching of first pathnodes".to_string()));
            }
        }
    }
    None
}

fn check_gainful_edges(
    instance: &Instance,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().cloned().collect_vec();
    let outside_edges = instance.out_edges();
    let all_edges = instance.all_edges();
    let npc = instance.npc();
    let outside_used_for_gain = instance.used_for_credit_gain();

    for &outside in outside_edges
        .iter()
        .filter(|e| !outside_used_for_gain.contains(e))
    {
        let out_pidx = nodes_to_pidx[outside.get_id() as usize].unwrap();
        let out_comp = &path_comps[out_pidx.raw()];

        let old_last = path_comps.first().unwrap();
        if old_last.comp.is_c4()
            || old_last.comp.is_c5()
            || old_last.comp.is_c6()
            || old_last.comp.is_c7()
        {
            for subpath in path_comps
                .iter()
                .permutations(path_comps.len() - 1)
                .filter(|p| p[0].path_idx == out_pidx && p.last() == path_comps.last().as_ref())
            {
                // subpath = [out_idx (end) -- ... -- rightmost enumerated comp (start)]

                let removed_comp = path_comps.iter().find(|c| !subpath.contains(c)).unwrap();

                let length = subpath.len();
                let first = subpath[0].clone();
                let cons_edges = subpath
                    .windows(2)
                    .map(|e| {
                        let idx1 = e[0].path_idx;
                        let idx2 = e[1].path_idx;
                        all_edges
                            .iter()
                            .filter(|e| e.between_path_nodes(idx1, idx2))
                            .map(|e| e.nodes_between_path_nodes(idx1, idx2))
                            .collect_vec()
                    })
                    .collect_vec();

                assert_eq!(length, cons_edges.len() + 1);

                let nice_paths = product_of_first(cons_edges).collect_vec();
                for nice_path in nice_paths {
                    // (0.in -- 1.out):(1.in -- 2.out):(2.in -- 3.out) ... (... -- start.out)
                    if valid_in_out_npc(
                        &first.comp,
                        &npc,
                        nice_path.first().unwrap().0,
                        outside,
                        true,
                        first.used,
                    ) {
                        let end = subpath[0].path_idx;
                        let end_in = nice_path.first().unwrap().0;
                        let start = subpath.last().unwrap().path_idx;
                        let start_out = nice_path.last().unwrap().1;

                        let mut inner = nice_path
                            .windows(2)
                            .enumerate()
                            .map(|(i, edges)| InOutNode {
                                in_node: edges[1].0,
                                idx: subpath[i + 1].path_idx,
                                out_node: edges[0].1,
                            })
                            .collect_vec();
                        // IMPORTANT
                        inner.reverse();

                        // extension [start.out -- .. -- 2.in:2.out -- 1.in:1.out -- end.in]
                        let extension = Extension {
                            start,
                            start_out,
                            end,
                            end_in,
                            inner,
                        };

                        let mut feasible = check_fixed_extension_feasible(
                            &extension,
                            &path_comps,
                            &npc,
                            false,
                            false,
                        );
                        feasible.eval();
                        if feasible.success() {
                            // if path_comps[1].comp.is_c6() && path_comps[2].comp.is_c5() {
                            //     println!("feasible extension {:?}", extension);
                            //     //panic!();
                            // }
                            // we have gainful edges

                            let (cases, gain) = match removed_comp.comp.comp_type() {
                                crate::comps::CompType::Cycle(4) => {
                                    let cases = out_comp
                                        .comp
                                        .nodes()
                                        .iter()
                                        .filter(|o| !out_comp.comp.is_adjacent(&outside, o))
                                        .cloned()
                                        .collect_vec();
                                    (cases, instance.context.inv.two_ec_credit(4))
                                }
                                crate::comps::CompType::Cycle(5) => {
                                    let cases = out_comp
                                        .comp
                                        .nodes()
                                        .iter()
                                        .filter(|&o| o != &outside)
                                        .cloned()
                                        .collect_vec();
                                    (cases, instance.context.inv.two_ec_credit(4))
                                }
                                crate::comps::CompType::Cycle(_) => (
                                    vec![outside],
                                    instance.context.inv.two_ec_credit(6) - Credit::from_integer(1),
                                ),
                                crate::comps::CompType::Large => (
                                    vec![outside],
                                    instance.context.inv.two_ec_credit(6) - Credit::from_integer(1),
                                ),
                                // crate::comps::CompType::Complex => {
                                //     panic!("no complex")
                                // }
                            };

                            // let cases = out_comp.comp.nodes().iter().filter(|o| !out_comp.comp.is_adjacent(&outside, o)).cloned().collect_vec();
                            // let gain = instance.context.inv.two_ec_credit(4);

                            let all_other_nodes = path_comps
                                .iter()
                                .filter(|comp| comp.path_idx != out_pidx)
                                .flat_map(|c| c.comp.nodes())
                                .filter(|n| {
                                    !all_edges.iter().any(|e| {
                                        e.node_incident(n)
                                            && e.node_incident(&outside)
                                            && e.cost <= Credit::from_integer(1) - gain
                                    })
                                })
                                .cloned()
                                .collect_vec();

                            // if path_comps.len() == 5 && path_comps[1].comp.is_c5() && path_comps[2].comp.is_c5() && path_comps[3].comp.is_c5() && path_comps[4].comp.is_c5() && outside_edges.contains(&Node::Node(5)) && outside_edges.contains(&Node::Node(15)) && outside_edges.contains(&Node::Node(12)){
                            //     info!("gainful edge at {}, cases {}, all_other {}, instance {}.", outside, cases.iter().join(","), all_other_nodes.iter().join(","), instance);
                            // }

                            if !all_other_nodes.is_empty() {
                                let iter =
                                    edge_iterator(cases.clone(), all_other_nodes, false, !finite);

                                let iter = to_cases_with_edge_cost(
                                    iter,
                                    nodes_to_pidx,
                                    instance,
                                    Credit::from_integer(1) - gain,
                                    false,
                                );
                                let iter = Box::new(iter.map(move |mut part| {
                                    for n in &cases {
                                        part.used_for_credit_gain.push(*n); // do not use this outside again
                                    }
                                    part
                                }));
                                return Some((
                                    Box::new(iter),
                                    format!("Gainful edge at node {}", outside),
                                ));
                            }
                        }
                    }
                }
            }
        }
    }

    None
}

fn check_four_matching(
    instance: &Instance,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().collect_vec();
    let len = path_comps.len();

    if finite {
        let path_comps = instance.path_nodes().collect_vec();

        for left_side in path_comps.into_iter().powerset().filter(|p| p.len() >= 2) {
            let comp_nodes = left_side
                .iter()
                .flat_map(|c| c.comp.nodes().to_vec())
                .collect_vec();

            let left_size: usize = left_side.iter().map(|comp| comp.comp.num_vertices()).sum();

            let left_large = left_side.iter().any(|c| c.comp.is_large());

            if left_size >= 10 && !left_large {
                if let Some(iter) = ensure_k_matching(comp_nodes, instance, 4, finite) {
                    let iter = to_cases(iter, nodes_to_pidx, instance, true);
                    return Some((iter, "4-Matching".to_string()));
                }
            }
        }
    } else {
        for left_side in path_comps
            .into_iter()
            .take(len - 2)
            .powerset()
            .filter(|p| p.len() >= 2)
        {
            let comp_nodes = left_side
                .iter()
                .flat_map(|c| c.comp.nodes().to_vec())
                .collect_vec();

            let left_size: usize = left_side.iter().map(|comp| comp.comp.num_vertices()).sum();

            let left_large = left_side.iter().any(|c| c.comp.is_large());

            if left_size >= 10 && !left_large {
                if let Some(iter) = ensure_k_matching(comp_nodes, instance, 4, finite) {
                    let iter = to_cases(iter, nodes_to_pidx, instance, true);
                    return Some((iter, "4-Matching".to_string()));
                }
            }
        }
    }

    None
}

fn check_comp_contractability(
    instance: &Instance,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().collect_vec();
    let len = path_comps.len();

    let iter = if finite {
        path_comps.iter().collect_vec()
    } else {
        path_comps.iter().take(len - 1).collect_vec()
    };
    let contractability_checked = instance.contractability_checked().collect_vec();
    for path_comp in iter {
        // TODO filter this differently
        if !(path_comp.comp.is_c4()
            || path_comp.comp.is_large()
            || (path_comp.comp.is_c5()
                && !path_comp.used
                && path_comp.path_idx.is_prelast()
                && !path_comp
                    .comp
                    .is_adjacent(&path_comp.in_node.unwrap(), &path_comp.out_node.unwrap())))
            && (!contractability_checked.contains(&&path_comp.path_idx))
        {
            if let Some(iter) =
                handle_contractable_components(path_comp, instance, finite, nodes_to_pidx.clone())
            {
                let idx = path_comp.path_idx;
                let iter = Box::new(iter.map(move |mut part| {
                    part.contractability_checked.push(idx);
                    part
                }));
                return Some((iter, format!("Contractablility of {}", idx)));
            }
        }
    }

    None
}

/// For the given pattern we say that a new edge is good if adding this edge to the instance guarantees progress for any superpattern.
/// Intuitively, we don't have to enumerate this edge again in any subpattern of this pattern.
fn compute_good_edges(
    instance: &mut Instance,
    finite: bool,
    iter: Box<dyn Iterator<Item = InstPart>>,
) -> Box<dyn Iterator<Item = InstPart>> {
    let mut good_edges = vec![];
    let mut good_out = vec![];

    let mut not_already_good = vec![];
    let parts = iter.collect_vec();
    for mut part in parts {
        if check_progress(instance, finite, part.clone()) {
            good_edges.append(&mut part.edges);
            good_out.append(&mut part.out_edges);
        } else {
            not_already_good.push(part);
        }
    }

    if let Some(top) = instance.top_mut() {
        top.good_edges.append(&mut good_edges);
        top.good_out.append(&mut good_out);
    }

    Box::new(not_already_good.into_iter())
}

fn to_cases_mul(
    iter: Box<dyn Iterator<Item = Vec<(Node, Hit)>>>,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    instance: &Instance,
    matching: bool,
) -> Box<dyn Iterator<Item = InstPart>> {
    to_cases_with_edge_cost_mul(
        iter,
        nodes_to_pidx,
        instance,
        Credit::from_integer(1),
        matching,
    )
}

fn to_cases(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    instance: &Instance,
    matching: bool,
) -> Box<dyn Iterator<Item = InstPart>> {
    to_cases_with_edge_cost(
        iter,
        nodes_to_pidx,
        instance,
        Credit::from_integer(1),
        matching,
    )
}

fn to_cases_with_edge_cost(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    instance: &Instance,
    cost: Credit,
    matching: bool,
) -> Box<dyn Iterator<Item = InstPart>> {
    let iter = Box::new(iter.map(|h| vec![h]));
    to_cases_with_edge_cost_mul(iter, nodes_to_pidx, instance, cost, matching)
}

fn to_cases_with_edge_cost_mul(
    iter: Box<dyn Iterator<Item = Vec<(Node, Hit)>>>,
    nodes_to_pidx: &Vec<Option<Pidx>>,
    instance: &Instance,
    cost: Credit,
    matching: bool,
) -> Box<dyn Iterator<Item = InstPart>> {
    let all_edges = instance.all_edges();

    let good_edges = instance.good_edges().into_iter().cloned().collect_vec();
    let good_out = instance.good_out().into_iter().cloned().collect_vec();

    let nodes_to_pidx = nodes_to_pidx.clone();

    let new_rem_id = instance.new_rem_id();
 

    let iter = Box::new(iter.flat_map(move |new_edges| {
        let mut part = InstPart::empty();

        let mut temp = new_rem_id;
        let mut new_rem_ids = vec![];
        for _ in 0..new_edges.len() {
            temp = temp.inc();
            new_rem_ids.push(temp);
        }
        
        for ((node, hit), id) in new_edges.into_iter().zip(new_rem_ids.into_iter()) {
            match hit {
                Hit::Outside => part.out_edges.push(node),
                Hit::RemPath => {
                    part.rem_edges.push(HalfAbstractEdge {
                        source: node,
                        source_idx: nodes_to_pidx[node.get_id() as usize].unwrap(),
                        cost,
                        id,
                        matching,
                    });
                }
                Hit::Node(hit_node) => {
                    if nodes_to_pidx[node.get_id() as usize].unwrap()
                        != nodes_to_pidx[hit_node.get_id() as usize].unwrap()
                    {
                        let edge = Edge::with_cost(
                            node,
                            nodes_to_pidx[node.get_id() as usize].unwrap(),
                            hit_node,
                            nodes_to_pidx[hit_node.get_id() as usize].unwrap(),
                            cost,
                        );
                        if !all_edges.contains(&edge) {
                            part.edges.push(edge);
                        }
                    }
                }
            }
        }

        if part.is_empty() {
            None
        } else {
            Some(part)
        }
    }));

    // Filter: consider only cases where edge are _not_ already good.
    Box::new(iter.filter(move |part| {
        if !part.edges.is_empty() {
            part.edges.iter().all(|edge| !good_edges.contains(edge))
        } else if !part.out_edges.is_empty() {
            part.out_edges.iter().all(|edge| !good_out.contains(edge))
        } else {
            true
        }
    }))
}

/// This method assumes that the given component already has a 3-matching.
fn handle_contractable_components(
    path_comp: &PathComp,
    instance: &Instance,
    finite: bool,
    nodes_to_pidx: Vec<Option<Pidx>>,
) -> Option<Box<dyn Iterator<Item = InstPart>>> {
    let comp = &path_comp.comp;

    let all_edges = instance.all_edges();
    let outside = instance.out_edges();
    let path_comps = instance.path_nodes().collect_vec();
    let rem_edges = instance.rem_edges();

    let nodes = comp.nodes();

    // nodes which are incident to some non-component edge, that is,
    // outside edges, back edges, in and out.
    let used_nodes = nodes
        .iter()
        .filter(|n| {
            outside.contains(n)
                || rem_edges.iter().any(|e| e.source == **n)
                || all_edges.iter().any(|e| e.node_incident(n))
                || (path_comp.in_node == Some(**n)
                    && !finite
                    && path_comp.path_idx != path_comps.last().unwrap().path_idx)
                || path_comp.out_node == Some(**n)
        })
        .cloned()
        .collect_vec();

    // free_nodes = nodes - used_nodes
    // have currently no incident edges
    let free_nodes = nodes
        .iter()
        .filter(|n| !used_nodes.contains(n))
        .cloned()
        .collect_vec();

    if free_nodes.len() <= 1 {
        // Not contractable
        return None;
    }
    if comp.is_c6() && free_nodes.len() <= 2 {
        // Not contractable
        return None;
    }

    let complement = path_comps
        .iter()
        .filter(|p| p.path_idx != path_comp.path_idx)
        .flat_map(|p| p.comp.nodes().to_vec())
        .collect_vec();

    let num_edges_between_free_nodes = comp
        .graph()
        .all_edges()
        .filter(|(u, v, _)| free_nodes.contains(u) && free_nodes.contains(v))
        .count();

    let opt_lb = free_nodes.len() * 2 - num_edges_between_free_nodes;

    if opt_lb * 5 >= comp.graph().node_count() * 4 {
        // component is 5/4-contractable!

        if comp.is_c5() {
            assert_eq!(free_nodes.len(), 2);
            assert!(!comp.is_adjacent(&free_nodes[0], &free_nodes[1]));

            //
            //     v3
            //   /    \
            //  f1    f2
            //   |    |
            //  v1 -- v2
            //
            let f1 = free_nodes[0];
            let f2 = free_nodes[1];
            let v3 = *comp
                .nodes()
                .iter()
                .find(|v| comp.is_adjacent(v, &f1) && comp.is_adjacent(v, &f2))
                .unwrap();
            let v1 = *comp
                .nodes()
                .iter()
                .find(|v| **v != v3 && comp.is_adjacent(v, &f1))
                .unwrap();
            let v2 = *comp
                .nodes()
                .iter()
                .find(|v| **v != v3 && comp.is_adjacent(v, &f2))
                .unwrap();

            assert!(comp.is_adjacent(&v1, &v2));
            assert!(!comp.is_adjacent(&v1, &v3));
            assert!(!comp.is_adjacent(&v3, &v2));

            assert!(!free_nodes.contains(&v1));
            assert!(!free_nodes.contains(&v2));
            assert!(!free_nodes.contains(&v3));

            // Case a) new nice pairs
            let case_a = vec![InstPart::new_nice_pairs(vec![(v1, v3), (v2, v3)])];

            // Case b) non-inside edges from f1 and f2
            let case_b = to_cases(
                edge_iterator(free_nodes, complement, true, !finite),
                &nodes_to_pidx,
                instance,
                false,
            );

            return Some(Box::new(case_a.into_iter().chain(case_b)));
        } else if comp.is_c6() {
            assert_eq!(free_nodes.len(), 3);
            let f1 = free_nodes[0];
            let f2 = free_nodes[1];
            let f3 = free_nodes[2];

            if !comp.is_adjacent(&f1, &f2)
                && !comp.is_adjacent(&f1, &f3)
                && !comp.is_adjacent(&f2, &f3)
            {
                //
                //     v1
                //   /    \
                //  f1    f2
                //   |    |
                //  v3    v2
                //   \    /
                //     f3
                let v1 = *comp
                    .nodes()
                    .iter()
                    .find(|v| comp.is_adjacent(v, &f1) && comp.is_adjacent(v, &f2))
                    .unwrap();
                let v2 = *comp
                    .nodes()
                    .iter()
                    .find(|v| comp.is_adjacent(v, &f2) && comp.is_adjacent(v, &f3))
                    .unwrap();
                let v3 = *comp
                    .nodes()
                    .iter()
                    .find(|v| comp.is_adjacent(v, &f1) && comp.is_adjacent(v, &f3))
                    .unwrap();

                // Case a) new nice pairs
                let case_a = vec![InstPart::new_nice_pairs(vec![(v1, v3), (v2, v3), (v1, v2)])];

                // Case b) edges from f1 and f2 and f3
                let case_b = to_cases(
                    edge_iterator(free_nodes, complement, true, !finite),
                    &nodes_to_pidx,
                    instance,
                    false,
                );

                return Some(Box::new(case_a.into_iter().chain(case_b)));
            }

            if free_nodes
                .iter()
                .combinations(2)
                .filter(|c| comp.is_adjacent(c[0], c[1]))
                .count()
                > 1
            {
                //
                //     f2
                //   /    \
                //  f1    f3
                //   |    |
                //  v3    v1
                //   \    /
                //     v2
                // Here we do nothing
                return None;
            }

            // This case remains:

            //      v1
            //   /      \
            // f2/f1    v2
            //   |       |
            // f1/f2    f3
            //   \      /
            //      v3

            let adj = free_nodes
                .iter()
                .combinations(2)
                .find(|adj| comp.is_adjacent(adj[0], adj[1]))
                .unwrap();
            let f1 = *adj[0];
            let f2 = *adj[1];
            let f3 = *free_nodes.iter().find(|f| !adj.contains(f)).unwrap();
            let v3 = *comp
                .nodes()
                .iter()
                .find(|v| {
                    comp.is_adjacent(v, &f3)
                        && (comp.is_adjacent(v, &f1) || comp.is_adjacent(v, &f2))
                })
                .unwrap();
            let v1 = *comp
                .nodes()
                .iter()
                .find(|v| {
                    !comp.is_adjacent(v, &f3)
                        && (comp.is_adjacent(v, &f1) || comp.is_adjacent(v, &f2))
                })
                .unwrap();
            let v2 = *comp
                .nodes()
                .iter()
                .find(|v| comp.is_adjacent(v, &v1) && comp.is_adjacent(v, &f3))
                .unwrap();

            // Case a) new nice pairs between v1,v2,v3
            let case_a = vec![
                InstPart::new_nice_pairs(vec![(v1, v3)]),
                InstPart::new_nice_pairs(vec![(v2, v3)]),
            ];

            // Case b) edges from f1 and f2 and f3
            let case_b = to_cases(
                edge_iterator(free_nodes, complement, true, !finite),
                &nodes_to_pidx,
                instance,
                false,
            );

            return Some(Box::new(case_a.into_iter().chain(case_b)));
        } else if comp.is_c7() {
            let num_cords =
                (opt_lb as f64 - comp.graph().node_count() as f64 * (4.0 / 5.0)).floor() as usize;
            // This follows from the assumption that the C7 must already have a 3-matching.
            // 1 <= num_cors <= 2
            assert!(num_cords <= 2);
            //assert!(num_cords >= 1);

            if num_cords >= 1 {
                let free_cords = free_nodes
                    .iter()
                    .combinations(2)
                    .filter(|c| !comp.is_adjacent(c[0], c[1]))
                    .collect_vec();

                let np_configs = free_cords
                    .iter()
                    .combinations(num_cords)
                    .map(|cords| {
                        let mut induced_nps = nodes
                            .iter()
                            .tuple_combinations()
                            .filter(|(u, v)| !comp.is_adjacent(u, v))
                            .filter(|(&u, &v)| {
                                // m is np if hamiltonian path exists
                                hamiltonian_paths(u, v, comp.nodes())
                                    .iter()
                                    .any(|path| is_path_in_comp(path, &cords, comp))
                            })
                            .map(|(u, v)| (*u, *v))
                            .collect_vec();
                        induced_nps.sort();
                        induced_nps
                    })
                    .unique()
                    .collect_vec();

                // Case a) new nice pair configs
                let case_a = np_configs
                    .into_iter()
                    .map(InstPart::new_nice_pairs)
                    .collect_vec();

                // Case b) edges from free nodes
                let iter = edge_iterator(free_nodes.clone(), complement.clone(), true, !finite);
                let comp = comp.clone();
                let iter = iter.flat_map(move |(node, hit)| {
                    if free_nodes.len() - 1 == 3
                        && free_nodes
                            .iter()
                            .filter(|f| **f != node)
                            .combinations(2)
                            .all(|fs| !comp.is_adjacent(fs[0], fs[1]))
                    {
                        // the remaining free nodes are pairwise not adjacent.
                        // in this case, enumerating this edge is not enough to break contractability
                        let other_free_nodes = free_nodes
                            .iter()
                            .filter(|f| f != &&node)
                            .cloned()
                            .collect_vec();
                        return edge_iterator(other_free_nodes, complement.clone(), true, !finite)
                            .map(|h| vec![(node, hit), h])
                            .collect_vec();
                    } else {
                        vec![vec![(node, hit)]]
                    }
                });
                let iter = Box::new(iter);
                let case_b = to_cases_mul(iter, &nodes_to_pidx, instance, false);

                return Some(Box::new(case_a.into_iter().chain(case_b)));
            }
        }
    }

    None
}

fn is_path_in_comp(path: &[Node], cords: &Vec<&Vec<&Node>>, comp: &Component) -> bool {
    path.windows(2).all(|e| {
        comp.is_adjacent(&e[0], &e[1])
            || cords.iter().any(|cord| {
                (*cord[0] == e[0] && *cord[1] == e[1]) || (*cord[1] == e[0] && *cord[0] == e[1])
            })
    })
}

fn ensure_three_matching(
    set1: Vec<Node>,
    instance: &Instance,
    finite: bool,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    ensure_k_matching(set1, instance, 3, finite)
}

/// Assumed that set1 is composed of all nodes of path comps
fn ensure_k_matching(
    set1: Vec<Node>,
    instance: &Instance,
    k: u8,
    finite: bool,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    let set2 = instance
        .all_nodes()
        .filter(|n| !set1.contains(n))
        .cloned()
        .collect_vec();

    let outside_edges_at_set = instance
        .out_edges()
        .iter()
        .filter(|n| set1.contains(n))
        .cloned()
        .collect_vec();
    let rem_edges_at_set = instance
        .rem_edges()
        .iter()
        .map(|e| e.source)
        .filter(|n| set1.contains(n))
        .collect_vec();
    let pattern_edges = instance.all_edges();
    let pattern_edges_between_sets = pattern_edges
        .iter()
        .filter(|e| e.one_sided_nodes_incident(&set1))
        .collect_vec();

    // 1. step: Compute and count unique non-comp nodes in set with outgoing or REM edges.
    // these are counted as matching edges!
    let non_comp_out_or_rem = set1
        .iter()
        .filter(|n| {
            !n.is_comp() && (outside_edges_at_set.contains(n) || rem_edges_at_set.contains(n))
        })
        .unique()
        .cloned()
        .collect_vec();

    // 2. step: Compute and count outgoing and REM edges at comp nodes in set.
    // these are counted as matching edges!
    let num_edges_comp_out_or_rem = outside_edges_at_set.iter().filter(|n| n.is_comp()).count()
        + rem_edges_at_set.iter().filter(|n| n.is_comp()).count();

    // 3. step: Num edges between comp nodes
    // these are counted as matching edges!
    let num_edges_between_comp = pattern_edges_between_sets
        .iter()
        .filter(|e| e.to_tuple().0.is_comp() && e.to_tuple().1.is_comp())
        .count();

    // 4. step: Compute pattern edges incident to at least one non-comp node
    let edges_incident_to_non_comp = pattern_edges_between_sets
        .iter()
        .filter(|e| !(e.to_tuple().0.is_comp() && e.to_tuple().1.is_comp()))
        .collect_vec();

    // all pattern edges with have an comp endpoint in set1 but a non-comp endpoint in set2 are counted as matching edges
    let num_edges_comp_at_set_non_comp_compl = edges_incident_to_non_comp
        .iter()
        .map(|e| e.endpoint_in(&set1).unwrap())
        .filter(|n| n.is_comp())
        .count();

    // 5. step: Compute minimal contribution to matching of edges in step 4
    let num_non_comp_at_set = edges_incident_to_non_comp
        .iter()
        .map(|e| e.endpoint_in(&set1).unwrap())
        .filter(|n| !n.is_comp() && !non_comp_out_or_rem.contains(n))
        .unique()
        .count();
    let non_comp_at_compl = edges_incident_to_non_comp
        .iter()
        .map(|e| e.endpoint_in(&set2).unwrap())
        .filter(|n| !n.is_comp())
        .unique()
        .collect_vec();
    let num_min_matching_between_non_comp = num_non_comp_at_set.min(non_comp_at_compl.len());

    if non_comp_out_or_rem.len()
        + num_edges_comp_out_or_rem
        + num_edges_between_comp
        + num_edges_comp_at_set_non_comp_compl
        + num_min_matching_between_non_comp
        < k as usize
    {
        let free_complement = set2
            .into_iter()
            .filter(|n| {
                n.is_comp()
                    || pattern_edges_between_sets
                        .iter()
                        .filter(|e| e.node_incident(n))
                        .count()
                        == 0
                // ) || (edges_incident_to_non_comp
                //     .iter()
                //     .filter(|e| e.node_incident(n))
                //     .count()
                //     > 1
                //     && non_comp_at_compl.len() < num_non_comp_at_set)
            })
            .collect_vec();

        let free_set = set1
            .into_iter()
            .filter(|n| {
                n.is_comp()
                    || (!non_comp_out_or_rem.contains(n)
                        && (pattern_edges_between_sets
                            .iter()
                            .filter(|e| e.node_incident(n))
                            .count()
                            == 0))
                // || (edges_incident_to_non_comp
                //     .iter()
                //     .filter(|e| e.node_incident(n))
                //     .count()
                //     > 1
                //     && non_comp_at_compl.len() > num_non_comp_at_set)))
            })
            .collect_vec();

        return Some(edge_iterator(free_set, free_complement, true, !finite));
    }

    None
}

fn edge_iterator(
    node_set: Vec<Node>,
    hit_set: Vec<Node>,
    with_outside: bool,
    with_rem: bool,
) -> Box<dyn Iterator<Item = (Node, Hit)>> {
    let mut hits = hit_set.into_iter().map(Hit::Node).collect_vec();
    if with_outside {
        hits.push(Hit::Outside);
    }
    if with_rem {
        hits.push(Hit::RemPath);
    }

    let iter = EdgeIterator::new(node_set, hits);
    Box::new(iter)
}

#[derive(Clone, Copy)]
enum Hit {
    Outside,
    RemPath,
    Node(Node),
}

struct EdgeIterator {
    nodes: Vec<Node>,
    hits: Vec<Hit>,
    current: Option<(usize, usize)>,
}

impl EdgeIterator {
    fn new(nodes: Vec<Node>, hits: Vec<Hit>) -> Self {
        Self {
            nodes,
            hits,
            current: None,
        }
    }
}

impl Iterator for EdgeIterator {
    type Item = (Node, Hit);

    fn next(&mut self) -> Option<Self::Item> {
        if let Some((mut c_node, mut c_hit)) = self.current {
            if c_hit < self.hits.len() - 1 {
                c_hit += 1;
            } else if c_node < self.nodes.len() - 1 {
                c_node += 1;
                c_hit = 0;
            } else {
                return None;
            }
            self.current = Some((c_node, c_hit));
            Some((self.nodes[c_node], self.hits[c_hit]))
        } else if self.nodes.is_empty() || self.hits.is_empty() {
            None
        } else {
            self.current = Some((0, 0));
            Some((self.nodes[0], self.hits[0]))
        }
    }
}

fn full_edge_iterator(
    node_set: Vec<Node>,
    hit_set: Vec<Node>,
    with_outside: bool,
    with_rem: bool,
    matching: bool,
) -> Box<dyn Iterator<Item = Vec<(Node, Hit)>>> {
    let mut hits = hit_set.into_iter().map(Hit::Node).collect_vec();
    if with_outside {
        if matching {
            for _ in &node_set {
                hits.push(Hit::Outside);
            }
        } else {
            hits.push(Hit::Outside);
        }
    }
    if with_rem {
        if matching {
            for _ in &node_set {
                hits.push(Hit::RemPath);
            }
        } else {
            hits.push(Hit::RemPath);
        }
    }

    let iter = FullEdgeIterator::new(node_set, hits, matching);
    Box::new(iter)
}

struct FullEdgeIterator {
    nodes: Vec<Node>,
    hits: Vec<Hit>,
    current_node_config: Option<Vec<Node>>,
    source_iter: Option<Box<dyn Iterator<Item = Vec<Node>>>>,
    hit_iter: Option<Box<dyn Iterator<Item = Vec<Hit>>>>,
    matching: bool,
}

impl FullEdgeIterator {
    fn new(nodes: Vec<Node>, hits: Vec<Hit>, matching: bool) -> Self {
        assert!(hits.len() >= nodes.len());
        Self {
            nodes,
            hits,
            current_node_config: None,
            source_iter: None,
            hit_iter: None,
            matching,
        }
    }
}

impl Iterator for FullEdgeIterator {
    type Item = Vec<(Node, Hit)>;

    fn next(&mut self) -> Option<Self::Item> {
        let len = self.nodes.len();
        if self.source_iter.is_none() {
            self.source_iter = Some(Box::new(self.nodes.clone().into_iter().permutations(len)));
            self.current_node_config = self.source_iter.as_mut().unwrap().next();
        }

        if self.hit_iter.is_none() {
            if self.matching {
                self.hit_iter = Some(Box::new(self.hits.clone().into_iter().combinations(len)))
            } else {
                self.hit_iter = Some(Box::new(
                    self.hits
                        .clone()
                        .into_iter()
                        .combinations_with_replacement(len),
                ))
            }
        }

        self.current_node_config.as_ref()?;

        if let Some(hit_iter) = &mut self.hit_iter {
            if let Some(hits) = hit_iter.next() {
                return Some(
                    self.current_node_config
                        .as_mut()
                        .unwrap()
                        .iter()
                        .cloned()
                        .zip(hits.iter().cloned())
                        .collect_vec(),
                );
            } else if let Some(sources) = self.source_iter.as_mut().unwrap().next() {
                self.current_node_config = Some(sources);
                if self.matching {
                    self.hit_iter = Some(Box::new(self.hits.clone().into_iter().combinations(len)))
                } else {
                    self.hit_iter = Some(Box::new(
                        self.hits
                            .clone()
                            .into_iter()
                            .combinations_with_replacement(len),
                    ))
                }
                let hits = self.hit_iter.as_mut().unwrap().next().unwrap();
                return Some(
                    self.current_node_config
                        .as_mut()
                        .unwrap()
                        .iter()
                        .cloned()
                        .zip(hits.iter().cloned())
                        .collect_vec(),
                );
            } else {
                return None;
            }
        }

        None
    }
}
