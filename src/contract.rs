use itertools::Itertools;
use petgraph::algo::connected_components;

use crate::{
    bridges::compute_bridges,
    comps::{EdgeType, Graph, Node},
};

pub fn first_twoec_subgraph(
    h: Graph,
    g: Graph,
    v1: u32,
    v2: u32,
    v3: u32,
) -> Option<Vec<(Node, Node)>> {
    debug_assert!(compute_bridges(&g).is_empty());
    debug_assert!(h.contains_node(v1));
    debug_assert!(h.contains_node(v2));
    debug_assert!(h.contains_node(v3));

    for buy in g
        .all_edges()
        .filter(|(u1, u2, _)| h.contains_node(*u1) && h.contains_node(*u2))
        .map(|(u1, u2, t)| (u1, u2, t))
        .powerset()
    {
        let mut graph = Graph::from_edges(buy.clone());
        for n in h.nodes() {
            graph.add_node(n);
        }
        graph.add_node(v1);
        graph.add_node(v2);
        graph.add_node(v3);
        let w1 = graph.nodes().max().unwrap() + 1;
        graph.add_node(w1);
        graph.add_edge(w1, v1, EdgeType::Fixed);
        graph.add_edge(w1, v2, EdgeType::Fixed);
        graph.add_edge(w1, v3, EdgeType::Fixed);

        if connected_components(&graph) == 1 && compute_bridges(&graph).is_empty() {
            return Some(buy.into_iter().map(|(v1, v2, _)| (v1, v2)).collect());
        }
    }

    None
}

#[cfg(test)]
mod test_contractibility {
    use super::*;

    #[test]
    fn test_six_cycle_odd() {
        let g = Graph::from_edges(vec![
            (0, 1, EdgeType::Sellable),
            (1, 2, EdgeType::Sellable),
            (2, 3, EdgeType::Sellable),
            (3, 4, EdgeType::Sellable),
            (4, 5, EdgeType::Sellable),
            (5, 0, EdgeType::Sellable),
        ]);
        let res = first_twoec_subgraph(g.clone(), g, 0, 2, 4);
        assert!(res.is_some());
        assert!(res.unwrap().len() == 6);
    }

    #[test]
    fn test_six_cycle_shortcut() {
        let g = Graph::from_edges(vec![
            (0, 1, EdgeType::Sellable),
            (1, 2, EdgeType::Sellable),
            (2, 3, EdgeType::Sellable),
            (3, 4, EdgeType::Sellable),
            (4, 5, EdgeType::Sellable),
            (5, 0, EdgeType::Sellable),
        ]);
        let res = first_twoec_subgraph(g.clone(), g, 0, 1, 4);
        assert!(res.is_some());
        assert!(res.unwrap().len() == 5);
    }

    #[test]
    fn test_six_cycle_with_string_odd() {
        let g = Graph::from_edges(vec![
            (0, 1, EdgeType::Sellable),
            (1, 2, EdgeType::Sellable),
            (2, 3, EdgeType::Sellable),
            (3, 4, EdgeType::Sellable),
            (4, 5, EdgeType::Sellable),
            (5, 0, EdgeType::Sellable),
            (1, 3, EdgeType::Sellable),
        ]);
        let res = first_twoec_subgraph(g.clone(), g, 0, 2, 4);
        assert!(res.is_some());
        assert!(res.unwrap().len() == 5);
    }
}
