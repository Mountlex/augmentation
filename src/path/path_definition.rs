use crate::{comps::Component, Node};

use super::NicePairConfig;

/// Checks whether a component satisfies the nice path definition
pub fn valid_in_out_npc(
    c: &Component,
    npc: &NicePairConfig,
    new_in: Node,
    new_out: Node,
    prelast: bool,
    used: bool,
) -> bool {
    if c.is_c4() {
        npc.is_nice_pair(new_in, new_out)
    } else if c.is_c5() && prelast && used {
        new_in != new_out
    } else if c.is_c5() && prelast && !used {
        npc.is_nice_pair(new_in, new_out)
    } else {
        true
    }
}

/// Checks whether a component satisfies the nice path definition, before we have enumerated nice pairs
pub fn valid_in_out_pre_npc(c: &Component, new_in: Node, new_out: Node, prelast: bool) -> bool {
    if c.is_c4() || (c.is_c5() && prelast) {
        new_in != new_out
    } else {
        true
    }
}
