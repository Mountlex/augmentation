use itertools::Itertools;

use crate::{
    comps::CompType,
    path::{extension::Extension, PathProofNode, Pidx, path_definition::valid_in_out_npc},
    path::{instance::Instance, NicePairConfig, PathComp},
};

// checked

pub fn check_path_rearrangement(instance: &Instance, finite: bool) -> PathProofNode {
    let rearrangement = instance.rearrangement().unwrap();

    let path_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    let mut feasible =
        check_fixed_extension_feasible(rearrangement, &path_comps, &npc, true, finite);
    feasible.eval();
    if !feasible.success() {
        feasible
    } else {
        let extension = rearrangement;

        let old_last_comp = &path_comps[Pidx::Last.raw()].comp;
        let new_last_comp = &path_comps[extension.end.raw()].comp;

        let order = [
            CompType::Cycle(5),
            CompType::Cycle(4),
            CompType::Large,
            CompType::Cycle(7),
            CompType::Cycle(6),
        ];
        // let order = [
        //     CompType::Large,
        //     CompType::Cycle(7),
        //     CompType::Cycle(6),
        //     CompType::Cycle(5),
        //     CompType::Cycle(4),
        // ];

        let old_type = old_last_comp.comp_type();
        let new_type = new_last_comp.comp_type();

        let old_pos = order
            .iter()
            .enumerate()
            .find(|(_, t)| t == &&old_type)
            .map(|(i, _)| i)
            .unwrap();
        let new_pos = order
            .iter()
            .enumerate()
            .find(|(_, t)| t == &&new_type)
            .map(|(i, _)| i)
            .unwrap();

        if new_pos < old_pos {
            return PathProofNode::new_leaf(
                format!(
                    "Rearrange cycle: now ends with {}!",
                    new_last_comp.short_name()
                ),
                true,
            );
        }

        PathProofNode::new_leaf(
            format!(
                "No feasible reduction (old_last = {}, new_last = {}",
                old_last_comp.short_name(),
                new_last_comp.short_name()
            ),
            false,
        )
    }
}

// Pidx here means the original pidx
pub fn check_fixed_extension_feasible(
    extension: &Extension,
    path_comps: &Vec<PathComp>,
    npc: &NicePairConfig,
    prelast_is_prelast: bool,
    finite: bool,
) -> PathProofNode {
    // extension: [start.out -- 1.in:1.out -- 2.in:2.out -- end.in]

    // check for inner zoomed nodes of extension that they fulfill nice path properties
    for (i, inner) in extension.inner.iter().enumerate() {
        let in_node = inner.in_node;
        let idx = inner.idx;
        let out_node = inner.out_node;

        let comp = &path_comps[idx.raw()];
        let valid_in_out = valid_in_out_npc(
            &comp.comp,
            npc,
            in_node,
            out_node,
            i == extension.inner.len() - 1 && prelast_is_prelast,
            comp.used,
        );
        if !valid_in_out {
            return PathProofNode::new_leaf(
                "New path does not fulfill nice path properties!".to_string(),
                false,
            );
        }
    }

    if !finite {
        // check if start connection fulfills nice path properties
        let start = extension.start;
        let start_out = extension.start_out;

        let start_comp = &path_comps[start.raw()];
        let valid_in_out = valid_in_out_npc(
            &start_comp.comp,
            npc,
            start_comp.in_node.unwrap(),
            start_out,
            extension.inner.is_empty() && prelast_is_prelast,
            start_comp.used,
        );
        if !valid_in_out {
            return PathProofNode::new_leaf(
                "New path does not fulfill nice path properties at rightmost vertex!".to_string(),
                false,
            );
        }
    }

    PathProofNode::new_leaf("Feasible path".into(), true)
}

