use itertools::Itertools;

use crate::{
    path::{
        enumerators::edges::edge_enumerator,
        instance::{InstPart, Instance, PathNode},
        path_definition::valid_in_out_pre_npc,
        PathComp, Pidx,
    },
    types::Edge,
    util::relabels_nodes_sequentially,
};

/// Splits the current pattern by adding one more component and considering all feasible in- out-
/// pairs between the previous first component and the new component
pub fn path_comp_enumerator(instance: &Instance) -> Box<dyn Iterator<Item = InstPart>> {
    let pattern_comps = instance.path_nodes().cloned().collect_vec();
    let all_comps = instance.context.comps.iter().cloned().collect_vec();

    assert!(!pattern_comps.is_empty());

    // Create a new case for every possible new component
    let iter = all_comps.into_iter().flat_map(move |new_comp| {
        let comp = new_comp.get_comp().clone();
        let num_used_labels = pattern_comps
            .iter()
            .map(|c| c.comp.num_labels())
            .sum::<usize>() as u32;
        let mut new_comps = vec![comp];
        relabels_nodes_sequentially(&mut new_comps, num_used_labels);
        let comp = new_comps.remove(0);
        let node = match new_comp {
            PathNode::Used(_) => PathNode::Used(comp.clone()),
            PathNode::Unused(_) => PathNode::Unused(comp.clone()),
        };

        // compute index for new comp
        let new_node_idx = pattern_comps.last().unwrap().path_idx.prec();

        // new comp has a fixed out node
        let out_nodes = vec![comp.fixed_node().unwrap()];

        // new comp has a list of possible in nodes
        let in_nodes = comp.in_nodes().to_vec(); //comp.matching_nodes().to_vec();

        // for any in_node of the new component
        let iter: Box<dyn Iterator<Item = PathComp>> =
            Box::new(in_nodes.into_iter().flat_map(move |in_node| {
                // copies for moves
                let comp_filter = comp.clone();
                let comp = comp.clone();
                let node = node.clone();

                // for all valid out_nodes of the new component
                let iter: Box<dyn Iterator<Item = PathComp>> = Box::new(
                    // case where we not consider the last node --> we need an out node
                    out_nodes
                        .clone()
                        .into_iter()
                        .filter(move |out_node| {
                            // only consider in-out combination which are possible in nice paths
                            valid_in_out_pre_npc(
                                &comp_filter,
                                in_node,
                                *out_node,
                                new_node_idx.is_prelast(),
                            )
                        })
                        .flat_map(move |out_node| {
                            let initial_nps = comp.edges();
                            let path_comp = PathComp {
                                comp: comp.clone(),
                                in_node: Some(in_node),
                                out_node: Some(out_node),
                                used: node.is_used(),
                                path_idx: new_node_idx,
                                initial_nps,
                            };

                            split_cases_by_required_nice_pairs(path_comp)
                        }),
                );
                iter
            }));

        iter.map(InstPart::new_path_comp)
    });

    Box::new(iter)
}

fn split_cases_by_required_nice_pairs(mut path_comp: PathComp) -> impl Iterator<Item = PathComp> {
    let comp = &path_comp.comp;
    let used = path_comp.used;
    let idx = path_comp.path_idx;
    let in_node = path_comp.in_node.unwrap();
    let out_node = path_comp.out_node.unwrap();

    // if in and out are adjacent we already have a nice pair
    if !comp.is_adjacent(&in_node, &out_node) {
        if comp.is_c4() {
            path_comp.initial_nps.push((in_node, out_node));
        }

        if comp.is_c5() && !used && idx.is_prelast() {
            //
            //    out
            //   /   \
            //   1   2
            //   |   |
            //  in - 3
            //
            let v1 = *comp
                .nodes()
                .iter()
                .find(|v| comp.is_adjacent(v, &in_node) && comp.is_adjacent(v, &out_node))
                .unwrap();
            let v2 = *comp
                .nodes()
                .iter()
                .find(|v| **v != v1 && comp.is_adjacent(v, &out_node))
                .unwrap();
            let v3 = *comp
                .nodes()
                .iter()
                .find(|v| **v != v1 && comp.is_adjacent(v, &in_node))
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
}

pub fn path_extension_enumerator(
    instance: &mut Instance,
) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
    let pattern_comps = instance.path_nodes().cloned().collect_vec();
    let back_edges = instance.rem_edges();

    if back_edges.is_empty() && pattern_comps.len() >= 3 {
        // If we cannot find more edges, and there are no rem edges, it wont help to enumerate more nodes.
        if edge_enumerator(instance, false).is_none() {
            log::info!("Enumerating more path nodes does not help!");
            return None;
        }
    }

    //let profile = instance.get_profile(true);
    //log::info!("Currently extending: {}", profile);

    let old_pattern_len = pattern_comps.len();

    // Enumerate components and in / out
    let iter = path_comp_enumerator(instance);

    // Enumerate back edges which might hit or don't hit the new component
    let iter: Box<dyn Iterator<Item = InstPart>> =
        Box::new(iter.into_iter().flat_map(move |inst_part| {
            let pattern_comps = pattern_comps.clone();
            let back_edges = back_edges.iter().cloned().collect_vec();
            back_edges
                .into_iter()
                .powerset()
                .flat_map(move |hitting_back_edges| {
                    let path_comp = inst_part.path_nodes.first().unwrap().clone();
                    let new_idx = inst_part.path_nodes.first().unwrap().path_idx;

                    // hitting_back_edges is the set of edges which should now hit the newly enumerated comp
                    let mut iter: Box<dyn Iterator<Item = InstPart>> =
                        Box::new(vec![InstPart::new_path_comp(path_comp.clone())].into_iter());

                    for i in 0..old_pattern_len {
                        let source_idx = Pidx::from(i);
                        //let source_comp = pattern_comps[source_idx.raw()].comp.clone();
                        let comp = path_comp.comp.clone();

                        // all matching edges between source_idx and node_idx
                        let matching_hit_back = hitting_back_edges
                            .clone()
                            .into_iter()
                            .filter(|e| e.source_idx == source_idx && e.matching)
                            .collect_vec();

                        let non_matching_hit_back = hitting_back_edges
                            .clone()
                            .into_iter()
                            .filter(|e| e.source_idx == source_idx && !e.matching)
                            .collect_vec();

                        let comp2 = comp.clone();

                        // First enumerate matching edges
                        if !matching_hit_back.is_empty() {
                            iter = Box::new(iter.flat_map(move |inst_part| {
                               
                                let matching_hit_back = matching_hit_back.clone();

                                let hitting_back_ids =
                                    matching_hit_back.iter().map(|e| e.id).collect_vec();

                                let comp_hit_matching_nodes_combinations =
                                    comp.combinations(matching_hit_back.len());

                                comp_hit_matching_nodes_combinations
                                    .into_iter()
                                    .filter(move |matched| {
                                        if source_idx.prec() == new_idx {
                                            if let Some(out) = path_comp.out_node {
                                                if out.is_comp() {
                                                    // this is the case where the next component is a large
                                                    true
                                                } else if !matched.contains(&out) {
                                                    // the in-out edge was also a matching edge
                                                    true
                                                } else {
                                                    false
                                                }
                                            } else {
                                                true
                                            }
                                        } else {
                                            true
                                        }
                                    })
                                    // .flat_map(|matched| {
                                    //     let len = matched.len();
                                    //     // the selected new edges can hit the new component in any permutation
                                    //     matched.into_iter().permutations(len)
                                    // })
                                    .map(move |matched| {
                                        let mut edges = matched
                                            .into_iter()
                                            .zip(matching_hit_back.iter())
                                            .map(|(u, v)| {
                                                Edge::new(v.source, source_idx, u, new_idx)
                                            })
                                            .collect_vec();

                                        let mut non_rem_edges = hitting_back_ids.clone();

                                        let mut inst_part_copy = inst_part.clone();
                                        inst_part_copy.edges.append(&mut edges);
                                        inst_part_copy.non_rem_edges.append(&mut non_rem_edges);

                                        inst_part_copy
                                    })
                            }));
                        }

                        let comp = comp2;

                        if !non_matching_hit_back.is_empty() {
                            iter = Box::new(iter.flat_map(move |inst_part| {
                                let non_matching_hit_back = non_matching_hit_back.clone();
                                let hitting_back_ids =
                                    non_matching_hit_back.iter().map(|e| e.id).collect_vec();

                                let comp_hit_non_matching_nodes_combinations =
                                    comp.combinations_with_replacement(non_matching_hit_back.len());

                                comp_hit_non_matching_nodes_combinations
                                    .into_iter()
                                    .filter(move |matched| {
                                        if source_idx.prec() == new_idx {
                                            if let Some(out) = path_comp.out_node {
                                                if out.is_comp() {
                                                    // this is the case where the next component is a large
                                                    true
                                                } else if !matched.contains(&out) {
                                                    // the in-out edge was also a matching edge
                                                    true
                                                } else {
                                                    false
                                                }
                                            } else {
                                                true
                                            }
                                        } else {
                                            true
                                        }
                                    })
                                    // .flat_map(|matched| {
                                    //     let len = matched.len();
                                    //     // the selected new edges can hit the new component in any permutation
                                    //     matched.into_iter().permutations(len)
                                    // })
                                    .map(move |matched| {
                                        let mut edges = matched
                                            .into_iter()
                                            .zip(non_matching_hit_back.iter())
                                            .map(|(u, v)| {
                                                Edge::new(v.source, source_idx, u, new_idx)
                                            })
                                            .collect_vec();

                                        let mut non_rem_edges = hitting_back_ids.clone();

                                        let mut inst_part_copy = inst_part.clone();
                                        inst_part_copy.edges.append(&mut edges);
                                        inst_part_copy.non_rem_edges.append(&mut non_rem_edges);

                                        inst_part_copy
                                    })
                            }));
                        }
                    }

                    iter
                })
        }));

    Some((Box::new(iter), "path node".into()))
}
