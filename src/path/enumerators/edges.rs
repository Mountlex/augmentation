use itertools::Itertools;

use crate::{
    path::{
        proof::Instance, util::contract::is_contractible, utils::hamiltonian_paths, InstPart,
        MatchingEdge, PathComp, Pidx,
    },
    types::Edge,
    Node,
};

use super::pseudo_cycles::pseudo_cycles_of_length;

pub fn edge_enumerator(
    instance: &mut Instance,
) -> Option<(Box<dyn Iterator<Item = InstPart> + '_>, String)> {
    let path_comps = instance.path_nodes().collect_vec();
    let old_path_len = path_comps.len();

    let mut nodes_to_pidx: Vec<Option<Pidx>> = vec![None; old_path_len * 20];
    for path_comp in &path_comps {
        for node in path_comp.comp.matching_nodes() {
            nodes_to_pidx[node.get_id() as usize] = Some(path_comp.path_idx.clone());
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
            to_inst_parts(iter, nodes_to_pidx, true, instance),
            format!("3-Matching of last pathnode."),
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
            let iter = to_inst_parts(iter, nodes_to_pidx, true, instance);
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
        if let Some(iter) = ensure_three_matching(comp_nodes, other_nodes, instance) {
            let iter = to_inst_parts(iter, nodes_to_pidx, true, instance);
            return Some((iter, format!("3-Matching of {} first pathnodes", s)));
        }
    }

    // Prio 4: Edges due to contractablility
    for path_comp in path_comps.iter().take(len - 1) {
        let idx = path_comp.path_idx;
        if let Some(iter) = handle_contractable_components(&path_comp, instance) {
            let iter = to_inst_parts(iter, nodes_to_pidx, false, instance);
            return Some((iter, format!("Contractablility of {}", idx)));
        }
    }

    // Prio 5: Larger contractable comps
    let all_edges = instance.all_edges();
    let relevant_comps = path_comps
        .iter()
        .filter(|c| c.comp.is_c3() || c.comp.is_c4() || c.comp.is_c5() || c.comp.is_c6())
        .cloned()
        .cloned()
        .collect_vec();
    for i in 3..=3 {
       // println!("Instance: {}", instance);
        for pc in
            pseudo_cycles_of_length(relevant_comps.clone(), all_edges.clone(), vec![], i, false)
        {
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
                        set.append(&mut comp.comp.nodes().into_iter().cloned().collect_vec())
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
                if let Some(good_verts) = is_contractible(&set, &instance) {
                    let all_nodes = instance
                        .path_nodes()
                        .flat_map(|c| c.comp.matching_nodes())
                        .filter(|n| !set.contains(n) ) //|| good_verts.contains(n))
                        .cloned()
                        .collect_vec();
                    
                   // println!("contractable set!: {:?}, good: {:?}", set, good_verts);

                    let iter = edge_iterator(good_verts.clone(), all_nodes).unwrap();
                    let iter = to_inst_parts(iter, nodes_to_pidx, false, instance).collect_vec();
                    //println!("iter: {}", iter.iter().join(", "));
                    return Some((Box::new(iter.into_iter()), format!("Contractablility of large set {:?}", set)));
                }
            }
        }
    }

    None
}

fn to_inst_parts(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: Vec<Option<Pidx>>,
    matching: bool,
    instance: &Instance,
) -> Box<dyn Iterator<Item = InstPart> + '_> {
    let all_edges = instance.all_edges();
    Box::new(iter.flat_map(move |(node, hit)| {
        let mut part = InstPart::empty();
    
        match hit {
            Hit::Outside => part.out_edges.push(node),
            Hit::RemPath => {
                part.rem_edges.push(MatchingEdge {
                    source: node,
                    source_idx: nodes_to_pidx[node.get_id() as usize].unwrap().clone(),
                    matching,
                    id: instance.matching_edge_id_counter.clone(),
                });
                //instance.matching_edge_id_counter.inc();
            }
            Hit::Node(hit_node) => {
                if nodes_to_pidx[node.get_id() as usize].unwrap()
                    != nodes_to_pidx[hit_node.get_id() as usize].unwrap() 
                {
                    let edge = Edge::new(
                        node,
                        nodes_to_pidx[node.get_id() as usize].unwrap().clone(),
                        hit_node,
                        nodes_to_pidx[hit_node.get_id() as usize].unwrap().clone(),
                    );
                    if !all_edges.contains(&edge) {
                        part.edges.push(edge);
                    }
                } 
            }
        }
        if part.is_empty() {
            return None
        } else {
            return Some(part)
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
    let outside = instance.out_edges().collect_vec();
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
        })
        .cloned()
        .collect_vec();
    let free_nodes = nodes
        .into_iter()
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

            return edge_iterator(free_nodes, complement);
        }
    }

    None
}

fn ensure_three_matching(
    set: Vec<Node>,
    compl: Vec<Node>,
    instance: &Instance,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    let outside_edges_at_set = instance
        .out_edges()
        .filter(|n| set.contains(n))
        .cloned()
        .collect_vec();
    let rem_edges_at_set = instance
        .rem_edges()
        .into_iter()
        .map(|e| e.source)
        .filter(|n| set.contains(n))
        .collect_vec();
    let edges_at_set = instance
        .all_edges()
        .into_iter()
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
        < 3
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

        return edge_iterator(free_set, free_complement);
    }

    None
}

fn edge_iterator(
    set: Vec<Node>,
    complement: Vec<Node>,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    let mut hits = complement.into_iter().map(|n| Hit::Node(n)).collect_vec();
    hits.push(Hit::Outside);
    hits.push(Hit::RemPath);

    let iter = set
        .into_iter()
        .flat_map(move |n1| hits.clone().into_iter().map(move |hit| (n1, hit)));

    return Some(Box::new(iter));
}
