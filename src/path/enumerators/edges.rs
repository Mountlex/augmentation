use itertools::Itertools;

use crate::{
    path::{
        enumerators::pseudo_cycles::{edges_between, product_of_first},
        proof::{check_progress, Instance},
        tactics::cycle_rearrange::{check_fixed_extension_feasible, valid_in_out_npc},
        util::contract::is_contractible,
        utils::hamiltonian_paths,
        HalfAbstractEdge, InstPart, PathComp, Pidx, NicePairConfig,
    },
    types::Edge,
    Node, Credit,
};

use super::pseudo_cycles::pseudo_cycles_of_length;

pub fn edge_enumerator(
    instance: &mut Instance,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let res = enumerate_parts(instance);

    if res.is_none() {
        return None;
    }

    let (iter, name) = res.unwrap();
    let cases = iter.collect_vec();
    let iter = compute_good_edges(instance, Box::new(cases.into_iter()));

    Some((iter, name))
}

struct InstanceInfo {
   path_comps: Vec<PathComp>,
   old_path_len: usize,
   outside_edges: Vec<Node>,
   all_edges: Vec<Edge>,
   npc: NicePairConfig,
   nodes_to_pidx: Vec<Option<Pidx>>
}

fn enumerate_parts(instance: &Instance) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().cloned().collect_vec();
    let old_path_len = path_comps.len();
    let outside_edges = instance.out_edges();
    let all_edges = instance.all_edges();
    let npc = instance.npc();

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
    if let Some(iter) = ensure_three_matching(last_nodes, other_nodes, instance) {
        return Some((
            to_cases(iter, nodes_to_pidx, instance),
            "3-Matching of last pathnode.".to_string(),
        ));
    }

    // Prio 2: Single 3-matchings
    let len = path_comps.len();
    //let mut path_comps = path_comps.into_iter().take(len - 1).collect_vec();
    //path_comps.sort_by_key(|p| p.comp.matching_nodes().len());
    for path_comp in path_comps.iter().skip(1).take(len - 2) {
        let idx = path_comp.path_idx;
        let comp_nodes = path_comp.comp.matching_nodes().to_vec();
        let other_nodes = path_comps
            .iter()
            .filter(|p| p.path_idx != path_comp.path_idx)
            .flat_map(|p| p.comp.matching_nodes().to_vec())
            .collect_vec();
        if let Some(iter) = ensure_three_matching(comp_nodes, other_nodes, instance) {
            let iter = to_cases(iter, nodes_to_pidx, instance);
            return Some((iter, format!("3-Matching of {}", idx)));
        }
    }

    

    // Prio 3.5.1: Gainful outside edges
    for outside in outside_edges {
        let out_pidx = nodes_to_pidx[outside.get_id() as usize].unwrap();

        for subpath in path_comps
            .iter()
            .permutations(path_comps.len() - 1)
            .filter(|p| p[0].path_idx == out_pidx && p.last() == path_comps.last().as_ref())
        {
            // subpath = [out_idx -- ... -- rightmost enumerated comp]

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
                if valid_in_out_npc(
                    &first.comp,
                    &npc,
                    nice_path.first().unwrap().0,
                    outside,
                    false,
                    first.used,
                ) {
                    if nice_path.len() > 1 {
                        let mut extension: Vec<(Option<Node>, Pidx, Option<Node>)> = vec![];
                        extension.push((Some(nice_path.first().unwrap().1), Pidx::Last, None));
                        for (i, w) in nice_path.windows(2).enumerate() {
                            extension.push((Some(w[1].0), Pidx::from(i + 1), Some(w[0].1)));
                        }
                        extension.reverse();

                        let mut feasible =
                            check_fixed_extension_feasible(&extension, &path_comps, &npc, false);
                        feasible.eval();
                        if feasible.success() {
                            // we have gainful edges
                            let old_last = path_comps.first().unwrap();
                            let gain = match old_last.comp.comp_type() {
                                crate::comps::CompType::Cycle(n) if n <= 5 => instance.context.inv.two_ec_credit(3),
                                crate::comps::CompType::Cycle(_) => instance.context.inv.two_ec_credit(6) - Credit::from(1),
                                crate::comps::CompType::Large => instance.context.inv.two_ec_credit(6) - Credit::from(1),
                                crate::comps::CompType::Complex => instance.context.inv.two_ec_credit(6) - Credit::from(1),
                            };

                            let all_other_nodes = path_comps.iter()
                                .filter(|comp| comp.path_idx != out_pidx)
                                .flat_map(|c| c.comp.matching_nodes())
                                .filter(|n| !all_edges.iter().any(|e| e.node_incident(n) && e.node_incident(&outside) && e.cost <= Credit::from(1) - gain))
                                .cloned()
                                .collect_vec();

                            // TODO care if there are already edges iwth 
                      
                            let iter = edge_iterator(vec![outside], all_other_nodes,false, true).unwrap();

                            

                            let iter = to_cases_with_edge_cost(iter, nodes_to_pidx, instance, Credit::from(1) - gain);
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
        if let Some(iter) = ensure_three_matching(comp_nodes, other_nodes, instance) {
            let iter = to_cases(iter, nodes_to_pidx, instance);
            return Some((iter, format!("3-Matching of {} first pathnodes", s)));
        }
    }

    

    // Prio 3.5: 4-matching
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
        if comp_nodes.len() >= 10 {
            if let Some(iter) = ensure_k_matching(comp_nodes, other_nodes, instance, 4) {
                let iter = to_cases(iter, nodes_to_pidx, instance);
                return Some((iter, format!("4-Matching of {} first pathnodes", s)));
            }
        }
    }


    // Prio 4: Edges due to contractablility
    for path_comp in path_comps.iter().take(len - 1) {
        let idx = path_comp.path_idx;
        if let Some(iter) = handle_contractable_components(path_comp, instance) {
            let iter = to_cases(iter, nodes_to_pidx, instance);
            return Some((iter, format!("Contractablility of {}", idx)));
        }
    }

    // Prio 5: Larger contractable comps
    let all_edges = instance.all_edges();
    let relevant_comps = path_comps
        .iter()
        .filter(|c| c.comp.is_c3() || c.comp.is_c4() || c.comp.is_c5() || c.comp.is_c6())
        .cloned()
        .collect_vec();
    for i in 3..=3 {
        // println!("Instance: {}", instance);
        for pc in pseudo_cycles_of_length(
            relevant_comps.clone(),
            None,
            all_edges.clone(),
            vec![],
            i,
            false,
        ) {
            //  println!("{}", pc);
            let mut vertices_sets = vec![vec![]];
            for (n1, c, n2) in pc.cycle {
                let idx = c.to_idx();
                let comp = relevant_comps
                    .iter()
                    .find(|comp| comp.path_idx == *idx)
                    .unwrap();
                if n1 == n2 {
                    vertices_sets.iter_mut().for_each(|set| set.push(n1));
                } else if comp.comp.is_adjacent(&n1, &n2) {
                    vertices_sets.iter_mut().for_each(|set| {
                        set.append(&mut comp.comp.nodes().iter().cloned().collect_vec())
                    });
                } else {
                    let (p1, p2) = comp.comp.paths_between(&n1, &n2);
                    // println!("set {:?}, p1 {:?}, p2 {:?}", vertices_sets, p1, p2);
                    vertices_sets = vertices_sets
                        .into_iter()
                        .flat_map(|set| {
                            vec![
                                vec![set.clone(), p1.clone()].concat(),
                                vec![set, p2.clone()].concat(),
                            ]
                        })
                        .collect_vec();
                }
            }

            for set in vertices_sets {
                if let Some(good_verts) = is_contractible(&set, instance) {
                    // G[set] is contractible
                    let all_nodes = instance
                        .path_nodes()
                        .flat_map(|c| c.comp.matching_nodes())
                        .filter(|n| !set.contains(n) || good_verts.contains(n))
                        .cloned()
                        .collect_vec();

                    // We now enumerate all edges which potentially resolve the contractability. Those are between the good vertices and
                    // (all vertices / bad vertices) (including good vertices)
                    let iter = edge_iterator(good_verts, all_nodes, true, true).unwrap();

                    let iter = to_cases(iter, nodes_to_pidx, instance);
                    //println!("iter: {}", iter.iter().join(", "));
                    return Some((
                        Box::new(iter),
                        format!("Contractablility of large set {:?}", set),
                    ));
                }
            }
        }
    }

    None
}

fn compute_good_edges(
    instance: &mut Instance,
    iter: Box<dyn Iterator<Item = InstPart>>,
) -> Box<dyn Iterator<Item = InstPart>> {
    let mut good_edges = vec![];
    let mut good_out = vec![];

    let mut rem_parts = vec![];
    let parts = iter.collect_vec();
    for mut part in parts {
        if check_progress(instance, part.clone()) {
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

    return Box::new(rem_parts.into_iter());
}

fn to_cases(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: Vec<Option<Pidx>>,
    instance: &Instance,
) -> Box<dyn Iterator<Item = InstPart>> {
    to_cases_with_edge_cost(
        iter,
        nodes_to_pidx,
        instance,
        Credit::from(1)
    )
}

fn to_cases_with_edge_cost(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: Vec<Option<Pidx>>,
    instance: &Instance,
    cost: Credit
) -> Box<dyn Iterator<Item = InstPart>> {
    let all_edges = instance.all_edges();

    let good_edges = instance.good_edges().into_iter().cloned().collect_vec();
    let good_out = instance.good_out().into_iter().cloned().collect_vec();

    let iter = Box::new(iter.flat_map(move |(node, hit)| {
        let mut part = InstPart::empty();

        match hit {
            Hit::Outside => part.out_edges.push(node),
            Hit::RemPath => {
                part.rem_edges.push(HalfAbstractEdge {
                    source: node,
                    source_idx: nodes_to_pidx[node.get_id() as usize].unwrap(),
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
                        cost
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
            !good_edges.contains(&part.edges.first().unwrap())
        } else if !part.out_edges.is_empty() {
            !good_out.contains(&part.out_edges.first().unwrap())
        } else {
            true
        }
    }))
}

#[derive(Clone)]
enum Hit {
    Outside,
    RemPath,
    Node(Node),
}

fn handle_contractable_components(
    path_comp: &PathComp,
    instance: &Instance,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    let comp = &path_comp.comp;

    let all_edges = instance.all_edges();
    let outside = instance.out_edges();
    let path_comps = instance.path_nodes().collect_vec();
    let rem_edges = instance.rem_edges();
    let npc = instance.npc();

    if comp.is_complex() || comp.is_large() || comp.is_c3() || comp.is_c4() {
        return None;
    }

    let nodes = comp.matching_nodes();
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
    let free_nodes = nodes
        .iter()
        .filter(|n| !used_nodes.contains(n))
        .cloned()
        .collect_vec();

    let num_edges_between_free_nodes = comp
        .graph()
        .all_edges()
        .filter(|(u, v, _)| free_nodes.contains(u) && free_nodes.contains(v))
        .count();

    let opt_lb = free_nodes.len() * 2 - num_edges_between_free_nodes;

    if opt_lb * 5 >= comp.graph().node_count() * 4 {
        let chord_implies_absent_np = free_nodes.iter().combinations(2).any(|free_edge| {
            used_nodes
                .iter()
                .combinations(2)
                .filter(|m| !npc.is_nice_pair(*m[0], *m[1]))
                .any(|m| {
                    hamiltonian_paths(*m[0], *m[1], comp.nodes())
                        .iter()
                        .any(|path| {
                            path.windows(2).all(|e| {
                                comp.is_adjacent(&e[0], &e[1])
                                    || (*free_edge[0] == e[0] && *free_edge[1] == e[1])
                                    || (*free_edge[1] == e[0] && *free_edge[0] == e[1])
                            })
                        })
                })
        });

        if chord_implies_absent_np {
            let complement = path_comps
                .iter()
                .filter(|p| p.path_idx != path_comp.path_idx)
                .flat_map(|p| p.comp.matching_nodes().to_vec())
                .collect_vec();

            return edge_iterator(free_nodes, complement, true, true);
        }
    }

    None
}

fn ensure_three_matching(
    set: Vec<Node>,
    compl: Vec<Node>,
    instance: &Instance,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    ensure_k_matching(set, compl, instance, 3)
}

fn ensure_k_matching(
    set: Vec<Node>,
    compl: Vec<Node>,
    instance: &Instance,
    k: u8,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    let outside_edges_at_set = instance
        .out_edges()
        .iter()
        .filter(|n| set.contains(n))
        .cloned()
        .collect_vec();
    let rem_edges_at_set = instance
        .rem_edges()
        .iter()
        .map(|e| e.source)
        .filter(|n| set.contains(n))
        .collect_vec();
    let edges = instance.all_edges();
    let edges_at_set = edges
        .iter()
        .filter(|e| e.one_sided_nodes_incident(&set))
        .collect_vec();

    // 1. step: Compute and count unique non-comp nodes in set with outgoing or REM edges.
    let non_comp_out_or_rem = set
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
        .map(|e| e.endpoint_in(&set).unwrap())
        .filter(|n| n.is_comp())
        .count();

    // 5. step: Compute minimal contribution to matching of edges in step 4
    let num_non_comp_at_set = edges_incident_to_non_comp
        .iter()
        .map(|e| e.endpoint_in(&set).unwrap())
        .filter(|n| !n.is_comp() && !non_comp_out_or_rem.contains(n))
        .unique()
        .count();
    let non_comp_at_compl = edges_incident_to_non_comp
        .iter()
        .map(|e| e.endpoint_in(&compl).unwrap())
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
        let free_complement = compl
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

        let free_set = set
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

        return edge_iterator(free_set, free_complement, true, true);
    }

    None
}

fn edge_iterator(
    set: Vec<Node>,
    complement: Vec<Node>,
    with_outside: bool,
    with_rem: bool,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    let mut hits = complement.into_iter().map(Hit::Node).collect_vec();
    if with_outside {
        hits.push(Hit::Outside);
    }
    if with_rem {
        hits.push(Hit::RemPath);
    }

    let iter = set
        .into_iter()
        .flat_map(move |n1| hits.clone().into_iter().map(move |hit| (n1, hit)));

    Some(Box::new(iter))
}
