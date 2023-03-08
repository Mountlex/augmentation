use itertools::Itertools;

use crate::{
    comps::Component,
    path::{proof::Instance, InstPart, PathComp, PathNode, Pidx},
    types::Edge,
    util::relabels_nodes_sequentially,
    Node,
};

// TODO READ
pub fn path_node_enumerator(instance: &Instance) -> Box<dyn Iterator<Item = InstPart> + '_> {
    let path_comps = instance.path_nodes().collect_vec();
    let old_path_len = path_comps.len();
    let all_edges = &instance.edges;
    let rem_edges = &instance.rem_edges;

    let iter = instance.context.comps.iter().flat_map(move |node| {
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

        let rem_edges = rem_edges.clone();
        let node_idx = path_comps.last().unwrap().path_idx.prec();

        let out_nodes = if let Some(fixed) = comp.fixed_node() {
            vec![fixed] // we assume here that if comp has a fixed node it was not used for any matching hit node.
        } else {
            let succ = node_idx.succ().unwrap();
            let matching_endpoints_at_new = all_edges
                .iter()
                .filter(|&edge| edge.between_path_nodes(succ, node_idx))
                .into_iter()
                .flat_map(|e| e.endpoint_at(node_idx))
                .collect_vec();

            comp.matching_nodes()
                .into_iter()
                .filter(|&n| !matching_endpoints_at_new.contains(n))
                .cloned()
                .collect_vec()
        };

        let in_nodes = if !node_idx.is_last() {
            comp.sym_matching_nodes().to_vec()
        } else {
            if let Some(fixed) = comp.fixed_node() {
                vec![fixed]
            } else {
                comp.sym_matching_nodes().to_vec()
            }
        };

        let comp_filter = comp.clone();
        let comp_map = comp.clone();
        let node_map = node.clone();

        let iter: Box<dyn Iterator<Item = PathComp>> =
            Box::new(in_nodes.into_iter().flat_map(move |in_node| {
                let comp_filter = comp_filter.clone();
                let comp_map = comp_map.clone();
                let node_map = node_map.clone();

                let iter: Box<dyn Iterator<Item = PathComp>> = Box::new(
                    // case where we not consider the last node --> we need an out node
                    out_nodes
                        .clone()
                        .into_iter()
                        .filter(move |out_node| {
                            prevalid_in_out(&comp_filter, in_node, *out_node, node_idx.is_prelast())
                        })
                        .map(move |out_node| PathComp {
                            comp: comp_map.clone(),
                            in_node: Some(in_node),
                            out_node: Some(out_node),
                            used: node_map.is_used(),
                            path_idx: node_idx,
                        }),
                );
                iter
            }));

        //println!("edges {:?}", all_edges);
        //println!("rem_edges {:?}", rem_edges);

        let iter: Box<dyn Iterator<Item = InstPart>> =
            Box::new(iter.into_iter().flat_map(move |path_comp| {
                let comp = comp.clone();
                let rem_edges_copy = rem_edges.iter().cloned().collect_vec();
                rem_edges_copy
                    .into_iter()
                    .powerset()
                    .flat_map(move |hits_node| {
                        let comp = comp.clone();

                        // hits_node is the set of edges which now should hit node_idx
                        let mut iter: Box<dyn Iterator<Item = InstPart>> =
                            Box::new(vec![InstPart::new_path_comp(path_comp.clone())].into_iter());
                        for i in 0..old_path_len {
                            let source_idx = Pidx::from(i);
                            let comp = comp.clone();

                            // all matching edges between source_idx and node_idx
                            let matching_edges = hits_node
                                .clone()
                                .into_iter()
                                .filter(|e| e.source_idx == source_idx)
                                .collect_vec();

                            let non_rem_edges =
                                hits_node.iter().map(|e| e.id.clone()).collect_vec();

                            iter = Box::new(iter.into_iter().flat_map(move |inst_part| {
                                let matching_edges = matching_edges.clone();
                                let non_rem_edges = non_rem_edges.clone();

                                comp.matching_permutations(matching_edges.len())
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
                                            .map(|(u, v)| {
                                                Edge::new(v.source, source_idx, u, node_idx)
                                            })
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

        iter
    });

    Box::new(iter)
}

fn prevalid_in_out(c: &Component, new_in: Node, new_out: Node, prelast: bool) -> bool {
    if c.is_c3() || c.is_c4() || (c.is_c5() && prelast) {
        new_in != new_out
    } else {
        true
    }
}
