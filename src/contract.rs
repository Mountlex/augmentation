use itertools::Itertools;
use petgraph::{visit::IntoEdgeReferences, data::Build};

use crate::{comps::Graph, bridges::compute_bridges};



pub fn first_two_ec_subgraph(h: Graph, g: Graph, v1: u32, v2: u32, v3: u32) {

    debug_assert!(compute_bridges(&g).is_empty());
    debug_assert!(h.contains_node(v1));
    debug_assert!(h.contains_node(v2));
    debug_assert!(h.contains_node(v3));

    for buy in g.edge_references().filter(|(u1,u2,_)| h.contains_node(*u1) && h.contains_node(*u2)).powerset() {
        let mut graph = Graph::from_edges(buy);
        
    }
}


