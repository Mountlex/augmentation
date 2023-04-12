use itertools::Itertools;

use crate::{
    comps::Component,
    path::{instance::Instance, proof::InstPart, NicePairConfig, PathComp},
    Node,
};

pub fn nice_pairs_enumerator(instance: &Instance) -> Box<dyn Iterator<Item = InstPart>> {
    let all_edges = instance.all_edges();
    let rem_edges = instance.rem_edges();
    let out_edges = instance.out_edges();


    let old_npc = instance.npc();

    let connected_nodes = instance.connected_nodes().cloned().collect_vec();

    let nodes_with_edges = all_edges
        .iter()
        .flat_map(|e| e.to_vec())
        .chain(rem_edges.iter().map(|e| e.source))
        .chain(out_edges.iter().cloned())
        .collect_vec();

    let mut cases: Box<dyn Iterator<Item = InstPart>> =
        Box::new(vec![InstPart::empty()].into_iter());

    let path_comps = instance.path_nodes().cloned().collect_vec();

    for path_comp in path_comps {
        let updated_nodes_with_edges = path_comp
            .comp
            .matching_nodes()
            .iter()
            .filter(|n| nodes_with_edges.contains(n))
            .cloned()
            .collect_vec();
        let path_comp_nodes = path_comp.comp.matching_nodes();
        let comp_conn_nodes = connected_nodes
            .iter()
            .filter(|n| path_comp_nodes.contains(n))
            .cloned()
            .collect_vec();

        let old_npc = old_npc.clone();

        cases = Box::new(cases.flat_map(move |inst_part| {
            let old_npc = old_npc.clone();
            let updated_nodes_with_edges = updated_nodes_with_edges.clone();

            let iter: Box<dyn Iterator<Item = InstPart>> =
                if comp_conn_nodes != updated_nodes_with_edges {
                    // node is already zoomed, just update nice pairs of new incident edges
                    let iter = comp_npcs(
                        &path_comp,
                        &updated_nodes_with_edges,
                        &old_npc,
                        &comp_conn_nodes,
                    )
                    .into_iter()
                    .map(move |mut npc| {
                      
                        let mut inst_part_clone = inst_part.clone();

                        inst_part_clone.nice_pairs.append(&mut npc.nice_pairs);
                        inst_part_clone.nice_pairs.sort();
                        inst_part_clone.nice_pairs.dedup();

                        inst_part_clone
                            .connected_nodes
                            .append(&mut updated_nodes_with_edges.clone());
                        inst_part_clone.connected_nodes.sort();
                        inst_part_clone.connected_nodes.dedup();

                        inst_part_clone
                    });
                    Box::new(iter)
                } else {
                    Box::new(vec![inst_part].into_iter())
                };
            iter
        }));
    }

    let cases = Box::new(cases.into_iter().map(move |mut part| {
        let nice_pairs = vec![old_npc.nice_pairs.clone(), part.nice_pairs.clone()].concat();
        part.nice_pairs = nice_pairs.into_iter().unique().collect_vec();
        part
    }));

    Box::new(cases)
}

// Compute all possible valid nice pair configurations
// - adjacent vertices are always nice pairs
// - in C3, C4 and C5 prelast used are in and out always nice pairs
fn comp_npcs(
    node: &PathComp,
    nodes: &[Node],
    consistent_npc: &NicePairConfig,
    consistent_nodes: &[Node],
) -> Vec<NicePairConfig> {
    let comp = &node.comp;

    match comp {
        Component::Large(_) => vec![NicePairConfig::empty()],
        Component::ComplexTree(_, black) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(v2))
                .collect_vec(),
        }],
        Component::ComplexPath(_, black) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(v2))
                .collect_vec(),
        }],
        _ => {
            // cycle case

            let mut npc = NicePairConfig {
                nice_pairs: comp.edges(),
            };
            if (comp.is_c3()
                || comp.is_c4()
                || (comp.is_c5() && !node.used && node.path_idx.is_prelast()))
                && node.in_node.is_some()
                && node.out_node.is_some()
            {
                npc.nice_pairs
                    .push((node.in_node.unwrap(), node.out_node.unwrap()))
            }
            return vec![npc];

            // TODO add all nice pairs

            // nodes
            //     .iter()
            //     .cloned()
            //     .tuple_combinations::<(_, _)>()
            //     .filter(|(u, v)| !comp.is_adjacent(u, v))
            //     .powerset()
            //     .map(|config| NicePairConfig { nice_pairs: config })
            //     .map(|mut npc| {
            //         // adjacent vertices are always nice pairs!
            //         npc.nice_pairs.append(&mut comp.edges()); // C3 in out contained here

            //         if (comp.is_c3()
            //             || comp.is_c4()
            //             || (comp.is_c5() && !node.used && node.path_idx.is_prelast()))
            //             && node.in_node.is_some()
            //             && node.out_node.is_some()
            //         {
            //             npc.nice_pairs
            //                 .push((node.in_node.unwrap(), node.out_node.unwrap()))
            //         }
            //         npc
            //     })
            //     .filter(|npc| npc.is_consistent_with(consistent_npc, consistent_nodes))
            //     .collect_vec()
        }
    }
}
