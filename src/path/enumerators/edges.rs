use itertools::Itertools;

use crate::path::extension::{Extension, InOutNode};
use crate::path::{instance::Instance, proof::InstPart};
use crate::{
    path::{
        enumerators::pseudo_cycles::product_of_first,
        proof::check_progress,
        tactics::cycle_rearrange::{check_fixed_extension_feasible, valid_in_out_npc},
        utils::hamiltonian_paths,
        HalfAbstractEdge, PathComp, Pidx,
    },
    types::Edge,
    Credit, Node,
};

pub fn edge_enumerator(
    instance: &mut Instance,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let res = enumerate_parts(instance, finite);

    //return res;

    res.as_ref()?;

    let (iter, name) = res.unwrap();
    let cases = iter.collect_vec();
    let iter = compute_good_edges(instance, finite, Box::new(cases.into_iter()));

    Some((iter, name))
}

// struct InstanceInfo {
//     path_comps: Vec<PathComp>,
//     old_path_len: usize,
//     outside_edges: Vec<Node>,
//     all_edges: Vec<Edge>,
//     npc: NicePairConfig,
//     nodes_to_pidx: Vec<Option<Pidx>>,
// }

fn enumerate_parts(
    instance: &Instance,
    finite: bool,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().cloned().collect_vec();
    let old_path_len = path_comps.len();
    let outside_edges = instance.out_edges();
    let all_edges = instance.all_edges();
    let npc = instance.npc();
    let outside_used_for_gain = instance.used_for_credit_gain();

    let mut nodes_to_pidx: Vec<Option<Pidx>> = vec![None; old_path_len * 20];
    for path_comp in &path_comps {
        for node in path_comp.comp.matching_nodes() {
            nodes_to_pidx[node.get_id() as usize] = Some(path_comp.path_idx);
        }
    }

    // Prio 1: Last comp gets 3-matching
    let last_nodes = path_comps.first().unwrap().comp.matching_nodes().to_vec();
    let other_nodes = path_comps
        .iter()
        .skip(1)
        .flat_map(|p| p.comp.matching_nodes().to_vec())
        .collect_vec();
    if let Some(iter) = ensure_three_matching(last_nodes, other_nodes, instance, finite) {
        return Some((
            to_cases(iter, nodes_to_pidx, instance),
            "3-Matching of last pathnode.".to_string(),
        ));
    }

    // Prio 2: Single 3-matchings
    let len = path_comps.len();
    //let mut path_comps = path_comps.into_iter().take(len - 1).collect_vec();
    //path_comps.sort_by_key(|p| p.comp.matching_nodes().len());
    let iter = if finite {
        path_comps.iter().collect_vec()
    } else {
        path_comps.iter().skip(1).take(len - 2).collect_vec()
    };
    for path_comp in iter {
        let idx = path_comp.path_idx;
        let comp_nodes = path_comp.comp.matching_nodes().to_vec();
        let other_nodes = path_comps
            .iter()
            .filter(|p| p.path_idx != path_comp.path_idx)
            .flat_map(|p| p.comp.matching_nodes().to_vec())
            .collect_vec();
        if let Some(iter) = ensure_three_matching(comp_nodes, other_nodes, instance, finite) {
            let iter = to_cases(iter, nodes_to_pidx, instance);
            return Some((iter, format!("3-Matching of {}", idx)));
        }
    }

    // Prio 3: Larger comps
    for s in 2..=len - 1 {
        let comp_nodes = path_comps
            .iter()
            .take(s)
            .flat_map(|c| c.comp.matching_nodes().to_vec())
            .collect_vec();
        let other_nodes = path_comps
            .iter()
            .filter(|p| p.path_idx.raw() >= s)
            .flat_map(|p| p.comp.matching_nodes().to_vec())
            .collect_vec();
        if let Some(iter) = ensure_three_matching(comp_nodes, other_nodes, instance, finite) {
            let iter = to_cases(iter, nodes_to_pidx, instance);
            return Some((iter, format!("3-Matching of {} first pathnodes", s)));
        }
    }

    // Prio 3.5.1: Gainful outside edges
    for &outside in outside_edges
        .iter()
        .filter(|e| !outside_used_for_gain.contains(e))
    {
        let out_pidx = nodes_to_pidx[outside.get_id() as usize].unwrap();
        let out_comp = &path_comps[out_pidx.raw()];

        let old_last = path_comps.first().unwrap();
        if old_last.comp.is_c4() {
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
                                crate::comps::CompType::Complex => {
                                    panic!("no complex")
                                }
                            };

                            // let cases = out_comp.comp.nodes().iter().filter(|o| !out_comp.comp.is_adjacent(&outside, o)).cloned().collect_vec();
                            // let gain = instance.context.inv.two_ec_credit(4);

                            let all_other_nodes = path_comps
                                .iter()
                                .filter(|comp| comp.path_idx != out_pidx)
                                .flat_map(|c| c.comp.matching_nodes())
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

    // Prio 3.5: 4-matching
    for s in 2..=len - 1 {
        let comp_nodes = path_comps
            .iter()
            .take(s)
            .flat_map(|c| c.comp.matching_nodes().to_vec())
            .collect_vec();

        let size: usize = path_comps
            .iter()
            .take(s)
            .map(|comp| comp.comp.num_vertices())
            .sum();

        let other_nodes = path_comps
            .iter()
            .filter(|p| p.path_idx.raw() >= s)
            .flat_map(|p| p.comp.matching_nodes().to_vec())
            .collect_vec();
        if size >= 10 {
            if let Some(iter) = ensure_k_matching(comp_nodes, other_nodes, instance, 4, finite) {
                let iter = to_cases(iter, nodes_to_pidx, instance);
                return Some((iter, format!("4-Matching of {} first pathnodes", s)));
            }
        }
    }

    // // Prio 4: Edges due to contractablility
    let iter = if finite {
        path_comps.iter().collect_vec()
    } else {
        path_comps.iter().take(len - 1).collect_vec()
    };
    let contractability_checked = instance.contractability_checked().collect_vec();
    for path_comp in iter {
        if !(path_comp.comp.is_c4()
            || path_comp.comp.is_large()
            || (path_comp.comp.is_c5()
                && !path_comp.used
                && path_comp.path_idx.is_prelast()
                && !path_comp
                    .comp
                    .is_adjacent(&path_comp.in_node.unwrap(), &path_comp.out_node.unwrap())))
            && (!contractability_checked.contains(&&path_comp.path_idx) || path_comp.comp.is_c7())
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

    // Prio 5: Larger contractable comps
    // let all_edges = instance.all_edges();
    // let relevant_comps = path_comps
    //     .iter()
    //     .filter(|c| c.comp.is_c3() || c.comp.is_c4() || c.comp.is_c5() || c.comp.is_c6())
    //     .cloned()
    //     .collect_vec();
    // for i in 3..=3 {
    //     // println!("Instance: {}", instance);
    //     for pc in pseudo_cycles_of_length(
    //         relevant_comps.clone(),
    //         None,
    //         all_edges.clone(),
    //         vec![],
    //         i,
    //         false,
    //     ) {
    //         //  println!("{}", pc);
    //         let mut vertices_sets = vec![vec![]];
    //         for (n1, c, n2) in pc.cycle {
    //             let idx = c.to_idx();
    //             let comp = relevant_comps
    //                 .iter()
    //                 .find(|comp| comp.path_idx == idx)
    //                 .unwrap();
    //             if n1 == n2 {
    //                 vertices_sets.iter_mut().for_each(|set| set.push(n1));
    //             } else if comp.comp.is_adjacent(&n1, &n2) {
    //                 vertices_sets.iter_mut().for_each(|set| {
    //                     set.append(&mut comp.comp.nodes().iter().cloned().collect_vec())
    //                 });
    //             } else {
    //                 let (p1, p2) = comp.comp.paths_between(&n1, &n2);
    //                 // println!("set {:?}, p1 {:?}, p2 {:?}", vertices_sets, p1, p2);
    //                 vertices_sets = vertices_sets
    //                     .into_iter()
    //                     .flat_map(|set| {
    //                         vec![
    //                             vec![set.clone(), p1.clone()].concat(),
    //                             vec![set, p2.clone()].concat(),
    //                         ]
    //                     })
    //                     .collect_vec();
    //             }
    //         }

    //         for set in vertices_sets {
    //             if let Some(good_verts) = is_contractible(&set, instance) {
    //                 // G[set] is contractible
    //                 let all_nodes = instance
    //                     .path_nodes()
    //                     .flat_map(|c| c.comp.matching_nodes())
    //                     .filter(|n| !set.contains(n) || good_verts.contains(n))
    //                     .cloned()
    //                     .collect_vec();

    //                 // We now enumerate all edges which potentially resolve the contractability. Those are between the good vertices and
    //                 // (all vertices / bad vertices) (including good vertices)
    //                 let iter = edge_iterator(good_verts, all_nodes, true, !finite).unwrap();

    //                 let iter = to_cases(iter, nodes_to_pidx, instance);
    //                 //println!("iter: {}", iter.iter().join(", "));
    //                 return Some((
    //                     Box::new(iter),
    //                     format!("Contractablility of large set {:?}", set),
    //                 ));
    //             }
    //         }
    //     }
    // }

    None
}

fn compute_good_edges(
    instance: &mut Instance,
    finite: bool,
    iter: Box<dyn Iterator<Item = InstPart>>,
) -> Box<dyn Iterator<Item = InstPart>> {
    let mut good_edges = vec![];
    let mut good_out = vec![];

    let mut rem_parts = vec![];
    let parts = iter.collect_vec();
    for mut part in parts {
        if check_progress(instance, finite, part.clone()) {
            good_edges.append(&mut part.edges);
            good_out.append(&mut part.out_edges);
        } else {
            rem_parts.push(part);
        }
    }

    if let Some(top) = instance.top_mut() {
        top.good_edges.append(&mut good_edges);
        top.good_out.append(&mut good_out);
    }

    Box::new(rem_parts.into_iter())
}

fn to_cases(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: Vec<Option<Pidx>>,
    instance: &Instance,
) -> Box<dyn Iterator<Item = InstPart>> {
    to_cases_with_edge_cost(iter, nodes_to_pidx, instance, Credit::from_integer(1))
}

fn to_cases_with_edge_cost(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: Vec<Option<Pidx>>,
    instance: &Instance,
    cost: Credit,
) -> Box<dyn Iterator<Item = InstPart>> {
    let all_edges = instance.all_edges();

    let good_edges = instance.good_edges().into_iter().cloned().collect_vec();
    let good_out = instance.good_out().into_iter().cloned().collect_vec();

    let new_rem_id = instance.new_rem_id();

    let iter = Box::new(iter.flat_map(move |(node, hit)| {
        let mut part = InstPart::empty();

        match hit {
            Hit::Outside => part.out_edges.push(node),
            Hit::RemPath => {
                part.rem_edges.push(HalfAbstractEdge {
                    source: node,
                    source_idx: nodes_to_pidx[node.get_id() as usize].unwrap(),
                    cost,
                    matching_with: vec![], // TODO
                    id: new_rem_id,
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
        if part.is_empty() {
            None
        } else {
            Some(part)
        }
    }));

    // Filter: consider only cases where edge are _not_ already good.
    Box::new(iter.filter(move |part| {
        if !part.edges.is_empty() {
            !good_edges.contains(part.edges.first().unwrap())
        } else if !part.out_edges.is_empty() {
            !good_out.contains(part.out_edges.first().unwrap())
        } else {
            true
        }
    }))
}

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

    let nodes = comp.matching_nodes();

    // nodes which are incident to some non-component edge
    let used_nodes = nodes
        .iter()
        .filter(|n| {
            outside.contains(n)
                || rem_edges.iter().any(|e| e.source == **n)
                || all_edges.iter().any(|e| e.node_incident(n))
                || path_comp.in_node == Some(**n)
                || path_comp.out_node == Some(**n)
        })
        .cloned()
        .collect_vec();

    // free_nodes = nodes - used_nodes
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
        .flat_map(|p| p.comp.matching_nodes().to_vec())
        .collect_vec();

    let num_edges_between_free_nodes = comp
        .graph()
        .all_edges()
        .filter(|(u, v, _)| free_nodes.contains(u) && free_nodes.contains(v))
        .count();

    let opt_lb = free_nodes.len() * 2 - num_edges_between_free_nodes;

    if opt_lb * 5 >= comp.graph().node_count() * 4 {
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
            let v3 = comp
                .nodes()
                .iter()
                .find(|v| comp.is_adjacent(v, &f1) && comp.is_adjacent(v, &f2))
                .unwrap()
                .clone();
            let v1 = comp
                .nodes()
                .iter()
                .find(|v| **v != v3 && comp.is_adjacent(v, &f1))
                .unwrap()
                .clone();
            let v2 = comp
                .nodes()
                .iter()
                .find(|v| **v != v3 && comp.is_adjacent(v, &f2))
                .unwrap()
                .clone();

            // Case a) new nice pairs
            let case_a = vec![InstPart::new_nice_pairs(vec![(v1, v3), (v2, v3)])];

            // Case b) edges from f1 and f2
            let case_b = to_cases(
                edge_iterator(free_nodes, complement, true, !finite),
                nodes_to_pidx,
                instance,
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
                let v1 = comp
                    .nodes()
                    .iter()
                    .find(|v| comp.is_adjacent(v, &f1) && comp.is_adjacent(v, &f2))
                    .unwrap()
                    .clone();
                let v2 = comp
                    .nodes()
                    .iter()
                    .find(|v| comp.is_adjacent(v, &f2) && comp.is_adjacent(v, &f3))
                    .unwrap()
                    .clone();
                let v3 = comp
                    .nodes()
                    .iter()
                    .find(|v| comp.is_adjacent(v, &f1) && comp.is_adjacent(v, &f3))
                    .unwrap()
                    .clone();

                // Case a) new nice pairs
                let case_a = vec![InstPart::new_nice_pairs(vec![(v1, v3), (v2, v3), (v1, v2)])];

                // Case b) edges from f1 and f2 and f3
                let case_b = to_cases(
                    edge_iterator(free_nodes, complement, true, !finite),
                    nodes_to_pidx,
                    instance,
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
                // Here we do nothing
                return None;
            }

            // This case remains:

            //     v1
            //   /    \
            //  f2    v2
            //   |    |
            //  f1    f3
            //   \    /
            //     v3

            // Case a) new nice pairs between v1,v2,v3
            let case_a = vec![InstPart::new_nice_pairs(
                used_nodes
                    .iter()
                    .combinations(2)
                    .map(|w| (*w[0], *w[1]))
                    .collect_vec(),
            )];

            // Case b) edges from f1 and f2 and f3
            let case_b = to_cases(
                edge_iterator(free_nodes, complement, true, !finite),
                nodes_to_pidx,
                instance,
            );

            return Some(Box::new(case_a.into_iter().chain(case_b)));
        } else if comp.is_c7() {
            let num_cords =
                (opt_lb as f64 - comp.graph().node_count() as f64 * (4.0 / 5.0)).floor() as usize;
            // 1 <= num_cors <= 2
            assert!(num_cords <= 2);
            assert!(num_cords >= 1);

            let all_possible_cords = free_nodes
                .iter()
                .combinations(2)
                .filter(|c| !comp.is_adjacent(c[0], c[1]))
                .collect_vec();

            let np_configs = all_possible_cords
                .iter()
                .combinations(num_cords)
                .map(|cords| {
                    let mut induced_nps = used_nodes
                        .iter()
                        .combinations(2)
                        .filter(|m| !comp.is_adjacent(m[0], m[1]))
                        .filter(|m| {
                            // m is np if hamiltonian path exists
                            hamiltonian_paths(*m[0], *m[1], comp.nodes())
                                .iter()
                                .any(|path| {
                                    path.windows(2).all(|e| {
                                        comp.is_adjacent(&e[0], &e[1])
                                            || cords.iter().any(|cord| {
                                                (*cord[0] == e[0] && *cord[1] == e[1])
                                                    || (*cord[1] == e[0] && *cord[0] == e[1])
                                            })
                                    })
                                })
                        })
                        .map(|m| (*m[0], *m[1]))
                        .collect_vec();
                    induced_nps.sort();
                    induced_nps
                })
                .collect_vec();

            // TODO we could throw some out?!

            // Case a) new nice pair configs
            let case_a = np_configs
                .into_iter()
                .map(|nps| InstPart::new_nice_pairs(nps))
                .collect_vec();

            // Case b) edges from free nodes
            let case_b = to_cases(
                edge_iterator(free_nodes, complement, true, !finite),
                nodes_to_pidx,
                instance,
            );

            return Some(Box::new(case_a.into_iter().chain(case_b)));
        }
    }

    None
}

fn ensure_three_matching(
    set1: Vec<Node>,
    set2: Vec<Node>,
    instance: &Instance,
    finite: bool,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    ensure_k_matching(set1, set2, instance, 3, finite)
}

fn ensure_k_matching(
    set1: Vec<Node>,
    set2: Vec<Node>,
    instance: &Instance,
    k: u8,
    finite: bool,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
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
    let edges = instance.all_edges();
    let edges_at_set = edges
        .iter()
        .filter(|e| e.one_sided_nodes_incident(&set1))
        .collect_vec();

    // 1. step: Compute and count unique non-comp nodes in set with outgoing or REM edges.
    let non_comp_out_or_rem = set1
        .iter()
        .filter(|n| {
            !n.is_comp() && (outside_edges_at_set.contains(n) || rem_edges_at_set.contains(n))
        })
        .unique()
        .cloned()
        .collect_vec();

    // 2. step: Compute and count outgoing and REM edges at comp notes in set.
    let num_edges_comp_out_or_rem = outside_edges_at_set.iter().filter(|n| n.is_comp()).count()
        + rem_edges_at_set.iter().filter(|n| n.is_comp()).count();

    // 3. step: Num edges between comp nodes
    let num_edges_between_comp = edges_at_set
        .iter()
        .filter(|e| e.to_tuple().0.is_comp() && e.to_tuple().1.is_comp())
        .count();

    // 4. step: Compute edges incident only to non-comp nodes
    let edges_incident_to_non_comp = edges_at_set
        .iter()
        .filter(|e| !(e.to_tuple().0.is_comp() && e.to_tuple().1.is_comp()))
        .collect_vec();

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
                n.is_comp() || edges_at_set.iter().filter(|e| e.node_incident(n)).count() == 0
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
                        && (edges_at_set.iter().filter(|e| e.node_incident(n)).count() == 0))
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
