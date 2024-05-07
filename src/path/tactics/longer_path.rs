use std::fmt::Write;

use itertools::Itertools;

use crate::{
    path::{
        extension::{Extension, InOutNode},
        path_definition::valid_in_out_npc,
        PathProofNode,
    },
    path::{instance::Instance, Pidx},
    util::product_of_first,
};

use super::cycle_rearrange::check_fixed_extension_feasible;

/// Check if we can find a longer nice path based on the currently enumerates edges
pub fn check_longer_nice_path(instance: &Instance, finite: bool) -> PathProofNode {
    let all_outside = instance.out_edges();
    let all_inter_comp_edges = instance.all_inter_comp_edges();
    let all_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    let mut msg = String::new();

    // ignore this for now. This is used if the program previously enumerated a rearrangement of the current nice path, then we would check if we can find a longer nice path based on this rearrangement
    if let Some(rearrangement) = instance.rearrangement() {
        let extension = rearrangement;

        let new_last_idx = extension.end;
        let new_last_comp = &all_comps[new_last_idx.raw()];
        let new_last_nodes = new_last_comp.comp.nodes();
        let outside_hits = all_outside.iter().filter(|n| new_last_nodes.contains(n));
        for outside_hit in outside_hits {
            // new_last will be prelast, check if end_in and outside_hit build feasible nice path
            if valid_in_out_npc(
                &new_last_comp.comp,
                &npc,
                extension.end_in,
                *outside_hit,
                true,
                new_last_comp.used,
            ) {
                let mut feasible =
                    check_fixed_extension_feasible(extension, &all_comps, &npc, false, finite);
                feasible.eval();
                if feasible.success() {
                    return PathProofNode::new_leaf(
                        format!(
                            "Longer nice path found via outside edge ({}) and cycle rearrangement!",
                            outside_hit
                        ),
                        true,
                    );
                } else {
                    msg.write_str("Extension is not feasible.").unwrap();
                }
            } else {
                msg.write_str(&format!("Rearr: {} is not valid out.", outside_hit))
                    .unwrap();
            }
        }
    }


    // We now check if the last comp has feasible outside edges with which we can extend the current nice path
    let last_comp = &all_comps[Pidx::Last.raw()];
    let last_comp_nodes = last_comp.comp.nodes();

    for outside_hit in all_outside.iter().filter(|n| last_comp_nodes.contains(n)) {
        // here we check we can use the currently last comp as prelast comp in a potential longer nice path. In particular, we check whether the in/out pair of this new prelast matches the requirements on the definition.
        if valid_in_out_npc(
            &last_comp.comp,
            &npc,
            last_comp.in_node.unwrap(),
            *outside_hit,
            true,
            last_comp.used,
        ) {
            // If we succeed, we essentially reached a leaf in the enumeration tree, and thus do not have to split the instance again.
            return PathProofNode::new_leaf(
                format!("Longer nice path found via outside edge ({})!", outside_hit),
                true,
            );
        }

        // If we have not succeed, we still want to find out whether we can use the outside_hit to extend the nice path. Since the previous check did not success, outside_hit and the current in-node of the last component did not satisfy the requirements. However, it could be that is some other edge e between last and prelast with which we could replace the edge (last.in, prelast.out), and with which we could try again whether outside_hit and e[last] are a valid in-out pair for the last component. However, if we do this, it could be that the current prelast component does no longer fullfil the nice path definition, because we changed its out-node, and so on. Thus, what we do is we enumerate all possible configurations of possible in-out edges between to consecutive components in the nice path. For each configuration we simply check whether it fulfills the nice path definition, and whether for the last component the new in-node and outside_hit are feasible.

        // this is list where the first entry is the list of all edges between path[0] and path[1], the second entry is the list of all edges between path[1] and path[2] ...
        let consecutive_edges = all_comps
            .windows(2)
            .map(|w| {
                all_inter_comp_edges
                    .iter()
                    .filter(|e| e.between_path_nodes(w[0].path_idx, w[1].path_idx))
                    .map(|e| {
                        if e.path_index_n1 == w[0].path_idx {
                            (e.n1, e.n2)
                        } else {
                            (e.n2, e.n1)
                        }
                    })
                    .collect_vec()
            })
            .collect_vec();

        if !consecutive_edges.is_empty() {
            // this product_of_first computes the cartesian product of the entries of consecutive_edges. That is, it gives us all configurations we need to check.
            let nice_paths = product_of_first(consecutive_edges).collect_vec();
            for nice_path in nice_paths {
                // nice path = [(0.in -- 1.out), (1.in -- 2.out), (2.in -- 3.out) ... (... -- start.out)]

                // we first check whether the last component can be extended with outside_hit in this configuration
                if valid_in_out_npc(
                    &last_comp.comp,
                    &npc,
                    nice_path.first().unwrap().0,
                    *outside_hit,
                    true,
                    last_comp.used,
                ) {
                    // if yes, we essentially check the rest via the method check_fixed_extension_feasible, which is also used at other places. It simply check for each component whether the nice path definition is satisfied.
                    // The next lines just convert nice_path into a different object, which we can feed into this method.
                    
                    let end = Pidx::Last;
                    let end_in = nice_path.first().unwrap().0;
                    let start = Pidx::from(nice_path.len());
                    let start_out = nice_path.last().unwrap().1;

                    let mut inner = nice_path
                        .windows(2)
                        .enumerate()
                        .map(|(i, edges)| InOutNode {
                            in_node: edges[1].0,
                            idx: Pidx::from(i + 1),
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

                    let mut feasible =
                        check_fixed_extension_feasible(&extension, &all_comps, &npc, false, finite);
                    feasible.eval();

                    // if this is also successful, we can again create a leaf in the enumeration tree.
                    if feasible.success() {
                        return PathProofNode::new_leaf(
                            format!(
                            "Longer nice path found via outside edge ({}) and path rearrangement!",
                            outside_hit
                        ),
                            true,
                        );
                    }
                }
            }
        }
    }

    // Ignore this for now.
    // TODO maybe unnecessary
    if finite {
        // check if last comp has feasible outside edges
        let mut rev_comps = all_comps.clone();
        rev_comps.reverse();
        let last_comp = &rev_comps[Pidx::Last.raw()];
        let last_comp_nodes = last_comp.comp.nodes();

        for outside_hit in all_outside.iter().filter(|n| last_comp_nodes.contains(n)) {
            if valid_in_out_npc(
                &last_comp.comp,
                &npc,
                last_comp.out_node.unwrap(),
                *outside_hit,
                true,
                last_comp.used,
            ) {
                return PathProofNode::new_leaf(
                    format!("Longer nice path found via outside edge ({})!", outside_hit),
                    true,
                );
            }

            let cons_edges = rev_comps
                .windows(2)
                .map(|w| {
                    all_inter_comp_edges
                        .iter()
                        .filter(|e| e.between_path_nodes(w[0].path_idx, w[1].path_idx))
                        .map(|e| {
                            if e.path_index_n1 == w[0].path_idx {
                                (e.n1, e.n2)
                            } else {
                                (e.n2, e.n1)
                            }
                        })
                        .collect_vec()
                })
                .collect_vec();

            if cons_edges.is_empty() {
                if valid_in_out_npc(
                    &last_comp.comp,
                    &npc,
                    last_comp.out_node.unwrap(),
                    *outside_hit,
                    true,
                    last_comp.used,
                ) {
                    return PathProofNode::new_leaf(
                        format!("Longer nice path found via outside edge ({})!", outside_hit),
                        true,
                    );
                }
            } else {
                let nice_paths = product_of_first(cons_edges).collect_vec();
                for nice_path in nice_paths {
                    // (0.in -- 1.out):(1.in -- 2.out):(2.in -- 3.out) ... (... -- start.out)
                    if valid_in_out_npc(
                        &last_comp.comp,
                        &npc,
                        nice_path.first().unwrap().0,
                        *outside_hit,
                        true,
                        last_comp.used,
                    ) {
                        let end = Pidx::Last;
                        let end_in = nice_path.first().unwrap().0;
                        let start = Pidx::from(nice_path.len());
                        let start_out = nice_path.last().unwrap().1;

                        let mut inner = nice_path
                            .windows(2)
                            .enumerate()
                            .map(|(i, edges)| InOutNode {
                                in_node: edges[1].0,
                                idx: Pidx::from(i + 1),
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
                            &extension, &rev_comps, &npc, false, finite,
                        );
                        feasible.eval();
                        if feasible.success() {
                            return PathProofNode::new_leaf(
                                format!(
                            "Longer nice path found via outside edge ({}) and path rearrangement!",
                            outside_hit
                        ),
                                true,
                            );
                        }
                    }
                }
            }
        }
    }


    // If we reach here, we could not prove that a longer nice path is possible, and thus return false

    PathProofNode::new_leaf(
        format!(
            "No outside matching hit does is a valid out edge for the last node: {}!",
            msg
        ),
        false,
    )
}
