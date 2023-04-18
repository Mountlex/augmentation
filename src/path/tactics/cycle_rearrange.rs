use itertools::Itertools;

use crate::{
    comps::Component,
    path::{PathProofNode, extension::Extension, Pidx},
    path::{instance::Instance, NicePairConfig, PathComp},
    Node,
};

pub fn check_path_rearrangement(instance: &Instance) -> PathProofNode {
    let rearrangement = instance.rearrangement().unwrap();

    let path_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    let mut feasible =
        check_fixed_extension_feasible(rearrangement, &path_comps, &npc, true);
    feasible.eval();
    if !feasible.success() {
        feasible
    } else {
        let extension = rearrangement;

        let old_last_comp = &path_comps[Pidx::Last.raw()].comp;
        let new_last_comp = &path_comps[extension.end.raw()].comp;

        // Complex > C5 > C4 > Large > C7 > C6 > C3

        // Reduce C3 to anything except C3
        if old_last_comp.is_c3() && !new_last_comp.is_c3() {
            return PathProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C6 to anything except C3 and C6
        if old_last_comp.is_c6() && !new_last_comp.is_c3() && !new_last_comp.is_c6() {
            return PathProofNode::new_leaf(
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
            return PathProofNode::new_leaf(
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
            return PathProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce C4 to C5
        if old_last_comp.is_c4() && new_last_comp.is_c5() {
            return PathProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        // Reduce anything that is not complex to complex
        if !old_last_comp.is_complex() && new_last_comp.is_complex() {
            return PathProofNode::new_leaf(
                format!("Rearrange cycle: now ends with {}!", new_last_comp),
                true,
            );
        }

        PathProofNode::new_leaf(
            format!(
                "No feasible reduction (old_last = {}, new_last = {}",
                old_last_comp, new_last_comp
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

    PathProofNode::new_leaf("Feasible path".into(), true)
}

pub fn valid_in_out_npc(
    c: &Component,
    npc: &NicePairConfig,
    new_in: Node,
    new_out: Node,
    prelast: bool,
    used: bool,
) -> bool {
    if c.is_c3() || c.is_c4() {
        npc.is_nice_pair(new_in, new_out)
    } else if c.is_c5() && prelast && used {
        new_in != new_out
    } else if c.is_c5() && prelast && !used {
        npc.is_nice_pair(new_in, new_out)
    } else if c.is_complex() {
        new_in != new_out || new_in.is_comp()
    } else {
        true
    }
}

