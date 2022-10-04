use crate::{
    comps::{Component, EdgeType},
    types::Edge,
    Graph,
};

pub fn get_merge_graph(comps: &[Component], edges: &[Edge]) -> Graph {
    let mut graph = Graph::new();
    for comp in comps {
        for (v1, v2, t) in comp.graph().all_edges() {
            graph.add_edge(v1, v2, *t);
        }
    }

    for e in edges {
        let (u, v) = e.to_tuple();
        graph.add_edge(u, v, EdgeType::Buyable);
    }
    graph
}
