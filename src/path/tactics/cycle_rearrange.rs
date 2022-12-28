use itertools::Itertools;

use crate::{
    comps::Component,
    path::{proof::Instance, NicePairConfig, PathComp, Pidx},
    proof_tree::ProofNode,
    Node,
};

pub fn check_path_rearrangement(instance: &Instance) -> ProofNode {
    let rearrangement = instance.rearrangement().unwrap();

    let path_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    let mut feasible =
        check_fixed_extension_feasible(&rearrangement.extension, &path_comps, &npc, true);
    feasible.eval();
    if !feasible.success() {
        return feasible;
    } else {
        let extension = &rearrangement.extension;

        let (_, old_last_idx, _) = extension.iter().find(|(_, idx, _)| idx.is_last()).unwrap();
        let old_last_comp = &path_comps[old_last_idx.raw()].comp;

        let new_last_idx = extension.last().unwrap().1;
        let new_last_comp = &path_comps[new_last_idx.raw()].comp;

        // Complex > C5 > C4 > Large > C7 > C6 > C3

        // Reduce C3 to anything except C3
        if old_last_comp.is_c3() && !new_last_comp.is_c3() {
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C6 to anything except C3 and C6
        if old_last_comp.is_c6() && !new_last_comp.is_c3() && !new_last_comp.is_c6() {
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C6 to anything except C3 and C6 and C7
        if old_last_comp.is_c7()
            && !new_last_comp.is_c3()
            && !new_last_comp.is_c6()
            && !new_last_comp.is_c7()
        {
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce Large to anything except C3 and C6 and C7 and Large
        if old_last_comp.is_large()
            && !new_last_comp.is_large()
            && !new_last_comp.is_c3()
            && !new_last_comp.is_c6()
            && !new_last_comp.is_c7()
        {
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C4 to C5
        if old_last_comp.is_c4() && new_last_comp.is_c5() {
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce anything that is not complex to complex
        if !old_last_comp.is_complex() && new_last_comp.is_complex() {
            return ProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        return ProofNode::new_leaf(
            format!(
                "No feasible reduction (old_last = {}, new_last = {}",
                old_last_comp, new_last_comp
            ),
            false,
        );
    }
}

pub fn check_fixed_extension_feasible(
    extension: &[(Option<Node>, Pidx, Option<Node>)],
    path_comps: &Vec<PathComp>,
    npc: &NicePairConfig,
    prelast_is_prelast: bool,
) -> ProofNode {
    // extension:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in]

    // check for inner zoomed nodes of extension that they fullfil nice path properties
    for i in 1..extension.len() - 1 {
        let (in_node, idx, out_node) = &extension[i];
        let comp = &path_comps[idx.raw()];
        let valid_in_out = valid_in_out_npc(
            &comp.comp,
            npc,
            in_node.unwrap(),
            out_node.unwrap(),
            i == extension.len() - 2 && prelast_is_prelast,
            comp.used,
        );
        if !valid_in_out {
            return ProofNode::new_leaf(
                format!("New path does not fulfill nice path properties!"),
                false,
            )
            .into();
        }
    }
    let (_, hit, hit_out) = extension.first().unwrap();
    let hit_comp = &path_comps[hit.raw()];
    valid_in_out_npc(
        &hit_comp.comp,
        npc,
        hit_comp.in_node.unwrap(),
        hit_out.unwrap(),
        extension.len() == 2 && prelast_is_prelast,
        hit_comp.used,
    );

    ProofNode::new_leaf("Feasible path".into(), true)
}

pub fn valid_in_out_npc(
    c: &Component,
    npc: &NicePairConfig,
    new_in: Node,
    new_out: Node,
    prelast: bool,
    used: bool,
) -> bool {
    if c.is_c3() || c.is_c4() || c.is_complex() {
        npc.is_nice_pair(new_in, new_out)
    } else if c.is_c5() && prelast && used {
        new_in != new_out
    } else if c.is_c5() && prelast && !used {
        npc.is_nice_pair(new_in, new_out)
    } else {
        true
    }
}

// fn check_matching_edge_extension_feasible(extension: &[SuperNode]) -> ProofNode {
//     let old_last_node = extension
//         .iter()
//         .find(|n| n.path_idx().is_last())
//         .unwrap()
//         .get_zoomed();
//     let old_last_comp = old_last_node.get_comp();

//     let hit = extension.first().unwrap();

//     // this is the case where we have an unexpanded matching edge

//     // old_last --- ... --- new_prelast --- new_last --- hit --- rem_path
//     //     |                                              |
//     //     -----------------------------------------------|
//     //                               matching edge

//     let new_prelast = &extension[extension.len() - 2];
//     let new_prelast_comp = new_prelast.get_comp();

//     if new_prelast_comp.is_c5() {
//         return ProofNode::new_leaf(
//             format!("New prelast is C5 but we cannot check nice path properties",),
//             false,
//         )
//         .into();
//     }
//     let old_last_np = old_last_node.npc.is_nice_pair(
//         old_last_node.in_node.unwrap(),
//         old_last_node.out_node.unwrap(),
//     );

//     if (old_last_comp.is_c3() || old_last_comp.is_c4()) && !old_last_np {
//         return ProofNode::new_leaf(
//             format!(
//                 "Cannot rearrange cycle: last comp is {} but has no nice pair!",
//                 old_last_comp
//             ),
//             false,
//         )
//         .into();
//     }

//     if let SuperNode::Abstract(hit_node) = hit {
//         let hit_comp = hit_node.get_comp();

//         if hit_comp.is_c3() || hit_comp.is_c4() {
//             // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
//             return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has nice pair in cycle, so we cannot guarantee nice pair on path!", hit_comp), false).into();
//         }
//     } else {
//         panic!()
//     }
//     ProofNode::new_leaf("Feasbile path".into(), true)
// }
