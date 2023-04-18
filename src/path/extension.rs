use std::fmt::Display;

use itertools::Itertools;

use crate::Node;

use super::Pidx;

/// start -- inner[0] -- inner[1] -- .. --- end
#[derive(Clone, Debug)]
pub struct Extension {
    pub start: Pidx,
    pub start_out: Node,
    pub end: Pidx,
    pub end_in: Node,
    pub inner: Vec<InOutNode>,
}

#[derive(Clone, Debug)]
pub struct InOutNode {
    pub in_node: Node,
    pub idx: Pidx,
    pub out_node: Node,
}

impl Display for InOutNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}-[{}]-{}", self.in_node, self.idx, self.out_node)
    }
}

impl Display for Extension {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Ext [ [{}]-{}", self.start, self.start_out)?;
        let inner = self.inner.iter().join(", ");
        write!(f, "{}", inner)?;
        write!(f, "{}-[{}] ]", self.end_in, self.end)
    }
}
