use crate::comps::Node;

#[derive(Copy, Clone, Debug, Default)]
pub struct Edge(pub Node, pub Node);

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        (self.0 == other.0 && self.1 == other.1) || (self.0 == other.1 && self.1 == other.0)
    }
}

impl Eq for Edge {}
