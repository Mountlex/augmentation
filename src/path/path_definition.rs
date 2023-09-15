use crate::{comps::Component, Node};

use super::NicePairConfig;

pub fn valid_in_out_npc(
    c: &Component,
    npc: &NicePairConfig,
    new_in: Node,
    new_out: Node,
    prelast: bool,
    used: bool,
) -> bool {
    if c.is_c3() || c.is_c4() || c.is_c5(){
        npc.is_nice_pair(new_in, new_out)
    // } else if c.is_c5() && prelast && used {
    //     new_in != new_out
    // } else if c.is_c5() && prelast && !used {
    //     npc.is_nice_pair(new_in, new_out)
    // // } else if c.is_complex() {
    // //     new_in != new_out || new_in.is_comp()
    } else {
        true
    }
}

pub fn valid_in_out_pre_npc(c: &Component, new_in: Node, new_out: Node, prelast: bool) -> bool {
    if c.is_c3() || c.is_c4() || c.is_c5() {
        //|| (c.is_c5() && prelast) {
        new_in != new_out
    // } else if c.is_complex() {
    //     new_in != new_out || new_in.is_comp()
    } else {
        true
    }
}
