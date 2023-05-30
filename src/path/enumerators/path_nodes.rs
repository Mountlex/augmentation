use itertools::Itertools;

use crate::{
    comps::Component,
    path::{
        enumerators::edges::edge_enumerator,
        instance::{Instance, InstPart, PathNode},
        PathComp, Pidx,
    },
    types::Edge,
    util::relabels_nodes_sequentially,
    Node,
};

pub fn path_comp_enumerator(instance: &Instance) -> Box<dyn Iterator<Item = InstPart>> {
    let path_comps = instance.path_nodes().cloned().collect_vec();
    let all_edges = instance.all_edges();
    let comps = instance.context.comps.iter().cloned().collect_vec();

    // for all component types...
    let iter = comps.into_iter().flat_map(move |node| {
        let comp = node.get_comp().clone();
        let num_used_labels = path_comps
            .iter()
            .map(|c| c.comp.num_labels())
            .sum::<usize>() as u32;
        let mut new_comps = vec![comp];
        relabels_nodes_sequentially(&mut new_comps, num_used_labels);
        let comp = new_comps.remove(0);
        let node = match node {
            PathNode::Used(_) => PathNode::Used(comp.clone()),
            PathNode::Unused(_) => PathNode::Unused(comp.clone()),
        };

        let node_idx = path_comps.last().unwrap().path_idx.prec();

        let out_nodes = if let Some(fixed) = comp.fixed_node() {
            vec![fixed] // we assume here that if comp has a fixed node it was not used for any matching hit node.
        } else {
            // this case is only for complex
            let succ = node_idx.succ().unwrap();
            let matching_endpoints_at_new = all_edges
                .iter()
                .filter(|&edge| edge.between_path_nodes(succ, node_idx))
                .flat_map(|e| e.endpoint_at(node_idx))
                .collect_vec();

            comp.matching_nodes()
                .iter()
                .filter(|&n| !matching_endpoints_at_new.contains(n))
                .cloned()
                .collect_vec()
        };

        let in_nodes = if !node_idx.is_last() {
            comp.in_nodes().to_vec()
        } else if let Some(fixed) = comp.fixed_node() {
            // if comp is last
            vec![fixed]
        } else {
            // only concerns complex
            comp.in_nodes().to_vec()
        };

        let comp_filter = comp.clone();
        let comp_map = comp;
        let node_map = node;

        // for all in_nodes of the new component
        let iter: Box<dyn Iterator<Item = PathComp>> =
            Box::new(in_nodes.into_iter().flat_map(move |in_node| {
                let comp_filter = comp_filter.clone();
                let comp_map = comp_map.clone();
                let node_map = node_map.clone();

                // for all valid out_nodes of the new component
                let iter: Box<dyn Iterator<Item = PathComp>> = Box::new(
                    // case where we not consider the last node --> we need an out node
                    out_nodes
                        .clone()
                        .into_iter()
                        .filter(move |out_node| {
                            prevalid_in_out(&comp_filter, in_node, *out_node, node_idx.is_prelast())
                        })
                        .flat_map(move |out_node| {
                            let new_nice_pairs = comp_map.edges();
                            let mut path_comp = PathComp {
                                comp: comp_map.clone(),
                                in_node: Some(in_node),
                                out_node: Some(out_node),
                                used: node_map.is_used(),
                                path_idx: node_idx,
                                initial_nps: new_nice_pairs,
                            };

                            if (comp_map.is_c4()
                                || (comp_map.is_c5()
                                    && !node_map.is_used()
                                    && node_idx.is_prelast()))
                                && !comp_map.is_adjacent(&in_node, &out_node)
                            {
                                // in and out must form a nice pair in comp!
                                if comp_map.is_c4() {
                                    path_comp.initial_nps.push((in_node, out_node));
                                }

                                if comp_map.is_c5() {
                                    //
                                    //    out
                                    //   /   \
                                    //   1   2
                                    //   |   |
                                    //  in - 3
                                    //
                                    let v1 = *comp_map
                                        .nodes()
                                        .iter()
                                        .find(|v| {
                                            comp_map.is_adjacent(v, &in_node)
                                                && comp_map.is_adjacent(v, &out_node)
                                        })
                                        .unwrap();
                                    let v2 = *comp_map
                                        .nodes()
                                        .iter()
                                        .find(|v| **v != v1 && comp_map.is_adjacent(v, &out_node))
                                        .unwrap();
                                    let v3 = *comp_map
                                        .nodes()
                                        .iter()
                                        .find(|v| **v != v1 && comp_map.is_adjacent(v, &in_node))
                                        .unwrap();

                                    path_comp.initial_nps.push((in_node, out_node));
                                    let mut p1 = path_comp.clone();
                                    let mut p2 = path_comp.clone();

                                    p1.initial_nps.push((v3, out_node));
                                    p2.initial_nps.push((v2, in_node));

                                    return vec![p1, p2].into_iter();
                                }
                            }
                            vec![path_comp].into_iter()
                        }),
                );
                iter
            }));

        iter.map(InstPart::new_path_comp)
    });

    Box::new(iter)
}

// TODO READ
pub fn path_extension_enumerator(
    instance: &mut Instance,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let path_comps = instance.path_nodes().cloned().collect_vec();
    let rem_edges = instance.rem_edges();

    if rem_edges.is_empty() && path_comps.len() >= 3 {
        // If we cannot find more edges, and there are no rem edges, it wont help to enumerate more nodes.
        if edge_enumerator(instance, false).is_none() {
            log::info!("Enumerating more path nodes does not help!");
            return None;
        }
    }

    //let profile = instance.get_profile(true);
    //log::info!("Currently extending: {}", profile);

    let old_path_len = path_comps.len();

    // Enumerate components and in / out
    let iter = path_comp_enumerator(instance);

    // Enumerate REM edges at new component
    let iter: Box<dyn Iterator<Item = InstPart>> =
        Box::new(iter.into_iter().flat_map(move |inst_part| {
            let rem_edges_copy = rem_edges.iter().cloned().collect_vec();
            rem_edges_copy
                .into_iter()
                .powerset()
                .flat_map(move |rem_edges_hit_new_node| {
                    let path_comp = inst_part.path_nodes.first().unwrap().clone();
                    let node_idx = inst_part.path_nodes.first().unwrap().path_idx;

                    // rem_edges_hit_new_node is the set of edges which now should hit node_idx
                    let mut iter: Box<dyn Iterator<Item = InstPart>> =
                        Box::new(vec![InstPart::new_path_comp(path_comp.clone())].into_iter());
                    for i in 0..old_path_len {
                        let source_idx = Pidx::from(i);
                        let comp = path_comp.comp.clone();

                        // all matching edges between source_idx and node_idx
                        let matching_edges = rem_edges_hit_new_node
                            .clone()
                            .into_iter()
                            .filter(|e| e.source_idx == source_idx)
                            .collect_vec();

                        // previous rem_edges which will be now realized are converted to non_rem_edges, so we collect those ids
                        let non_rem_edges =
                            rem_edges_hit_new_node.iter().map(|e| e.id).collect_vec();

                        iter = Box::new(iter.flat_map(move |inst_part| {
                            let matching_edges = matching_edges.clone();
                            let non_rem_edges = non_rem_edges.clone();

                            //comp.subsets_of_size(matching_edges.len())
                            comp.combinations_with_replacement(matching_edges.len())
                                .into_iter()
                                .filter(move |matched| {
                                    if source_idx.prec() == node_idx {
                                        if let Some(out) = path_comp.out_node {
                                            out.is_comp()
                                                || matched.iter().all(|matched| *matched != out)
                                        } else {
                                            true
                                        }
                                    } else {
                                        true
                                    }
                                })
                                .map(move |matched| {
                                    let mut edges = matched
                                        .into_iter()
                                        .zip(matching_edges.iter())
                                        .map(|(u, v)| Edge::new(v.source, source_idx, u, node_idx))
                                        .collect_vec();

                                    let mut non_rem_edges = non_rem_edges.clone();

                                    let mut inst_part_copy = inst_part.clone();
                                    inst_part_copy.edges.append(&mut edges);
                                    inst_part_copy.non_rem_edges.append(&mut non_rem_edges);

                                    inst_part_copy
                                })
                        }))
                    }

                    iter
                })
        }));

    Some((Box::new(iter), "path node".into()))
}

fn prevalid_in_out(c: &Component, new_in: Node, new_out: Node, prelast: bool) -> bool {
    if c.is_c3() || c.is_c4() || (c.is_c5() && prelast) {
        new_in != new_out
    } else if c.is_complex() {
        new_in != new_out || new_in.is_comp()
    } else {
        true
    }
}
