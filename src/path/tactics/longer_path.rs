use std::fmt::Write;

use itertools::Itertools;

use crate::{
    path::PathProofNode,
    path::{enumerators::pseudo_cycles::product_of_first, proof::Instance, Pidx},
    Node,
};

use super::cycle_rearrange::{check_fixed_extension_feasible, valid_in_out_npc};

pub fn check_longer_nice_path(instance: &Instance) -> PathProofNode {
    let all_outside = instance.out_edges();
    let all_edges = instance.all_edges();
    let all_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    // TODO better error messages
    let mut msg = String::new();

    if let Some(rearrangement) = instance.rearrangement() {
        let extension = &rearrangement.extension;

        let new_last_idx = extension.last().unwrap().1;
        let new_last_comp = &all_comps[new_last_idx.raw()];
        let new_last_nodes = new_last_comp.comp.matching_nodes();
        let outside_hits = all_outside.iter().filter(|n| new_last_nodes.contains(n));
        for outside_hit in outside_hits {
            // new_last will be prelast
            if valid_in_out_npc(
                &new_last_comp.comp,
                &npc,
                extension.last().unwrap().0.unwrap(),
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
                    msg.write_str("Extension is not feasible.")
                        .unwrap();
                }
            } else {
                msg.write_str(&format!("Rearr: {} is not valid out.", outside_hit))
                    .unwrap();
            }
        }
    }

    let last_comp = all_comps.first().unwrap();
    let last_comp_nodes = last_comp.comp.matching_nodes();
    let path_len = all_comps.len();

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

        let nice_paths = product_of_first(cons_edges).collect_vec();
        for nice_path in nice_paths {
            if valid_in_out_npc(
                &last_comp.comp,
                &npc,
                nice_path.first().unwrap().0,
                *outside_hit,
                true,
                last_comp.used,
            ) {
                if nice_path.len() > 1 {
                    let mut extension: Vec<(Option<Node>, Pidx, Option<Node>)> = vec![];
                    extension.push((Some(nice_path.first().unwrap().1), Pidx::Last, None));
                    for (i, w) in nice_path.windows(2).enumerate() {
                        extension.push((Some(w[1].0), Pidx::from(i + 1), Some(w[0].1)));
                    }
                    extension.reverse();

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
                } else {
                    return PathProofNode::new_leaf(
                        format!("Longer nice path found via outside edge ({})!", outside_hit),
                        true,
                    );
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
