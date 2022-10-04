use crate::{comps::Component, Graph, Node};

pub fn relabels_nodes_sequentially(comps: &mut [Component], mut offset: u32) {
    for comp in comps {
        match comp {
            Component::C6(nodes) => offset += relabel_slice(nodes, offset),
            Component::C5(nodes) => offset += relabel_slice(nodes, offset),
            Component::C4(nodes) => offset += relabel_slice(nodes, offset),
            Component::C3(nodes) => offset += relabel_slice(nodes, offset),
            Component::Large(n) => {
                n.set_id(offset);
                offset += 1;
            }
            Component::ComplexPath(c, blacks) => {
                c.graph = Graph::from_edges(c.graph.all_edges().map(|(mut w1, mut w2, t)| {
                    w1.inc_id(offset);
                    w2.inc_id(offset);
                    (w1, w2, *t)
                }));
                blacks.iter_mut().for_each(|n| n.inc_id(offset));
                offset += c.graph.node_count() as u32;
            }
            Component::ComplexTree(c, blacks) => {
                c.graph = Graph::from_edges(c.graph.all_edges().map(|(mut w1, mut w2, t)| {
                    w1.inc_id(offset);
                    w2.inc_id(offset);
                    (w1, w2, *t)
                }));
                blacks.iter_mut().for_each(|n| n.inc_id(offset));
                offset += c.graph.node_count() as u32;
            }
        }
    }
}

fn relabel_slice(slice: &mut [Node], offset: u32) -> u32 {
    slice.iter_mut().for_each(|n| n.inc_id(offset));
    slice.len() as u32
}
