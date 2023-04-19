use std::fmt::Write;

use itertools::Itertools;

use crate::{
    path::{enumerators::pseudo_cycles::product_of_first, instance::Instance, Pidx},
    path::{
        extension::{Extension, InOutNode},
        PathProofNode,
    },
};

use super::cycle_rearrange::{check_fixed_extension_feasible, valid_in_out_npc};

// checked

pub fn check_longer_nice_path(instance: &Instance) -> PathProofNode {
    let all_outside = instance.out_edges();
    let all_edges = instance.all_edges();
    let all_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    // TODO better error messages
    let mut msg = String::new();

    if let Some(rearrangement) = instance.rearrangement() {
        let extension = rearrangement;

        let new_last_idx = extension.end;
        let new_last_comp = &all_comps[new_last_idx.raw()];
        let new_last_nodes = new_last_comp.comp.matching_nodes();
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
                    check_fixed_extension_feasible(extension, &all_comps, &npc, false);
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

    // check if last comp has feasible outside edges
    let last_comp = &all_comps[Pidx::Last.raw()];
    let last_comp_nodes = last_comp.comp.matching_nodes();

    for outside_hit in all_outside.iter().filter(|n| last_comp_nodes.contains(n)) {
        let cons_edges = all_comps
            .windows(2)
            .map(|w| {
                all_edges
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
                last_comp.in_node.unwrap(),
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

                    let mut feasible =
                        check_fixed_extension_feasible(&extension, &all_comps, &npc, false);
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

    PathProofNode::new_leaf(
        format!(
            "No outside matching hit does is a valid out edge for the last node: {}!",
            msg
        ),
        false,
    )
}
