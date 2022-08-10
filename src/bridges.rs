use petgraph::visit::{
    depth_first_search, Control, DfsEvent, IntoNeighbors, IntoNodeIdentifiers, NodeIndexable,
    Visitable,
};

pub fn compute_bridges<G>(g: G) -> Vec<(G::NodeId, G::NodeId)>
where
    G: IntoNeighbors + Visitable + IntoNodeIdentifiers + NodeIndexable,
    G::NodeId: std::fmt::Debug,
{
    let mut parent = vec![None; g.node_bound()];
    let mut disc = vec![0; g.node_bound()];
    let mut low = vec![0; g.node_bound()];
    let mut bridges = vec![];

    if let Some(start) = g.node_identifiers().next() {
        depth_first_search(&g, Some(start), |event| -> Control<()> {
            match event {
                DfsEvent::TreeEdge(u, v) => {
                    parent[g.to_index(v)] = Some(u);
                }
                DfsEvent::Discover(u, time) => {
                    low[g.to_index(u)] = time.0;
                    disc[g.to_index(u)] = time.0;
                }
                DfsEvent::Finish(v, _) => {
                    if let Some(u) = parent[g.to_index(v)] {
                        low[g.to_index(u)] = low[g.to_index(v)].min(low[g.to_index(u)]);

                        if low[g.to_index(v)] > disc[g.to_index(u)] {
                            bridges.push((v, u));
                        }
                    }
                }
                DfsEvent::BackEdge(u, v) | DfsEvent::CrossForwardEdge(u, v) => {
                    if parent[g.to_index(u)] != Some(v) {
                        low[g.to_index(u)] = disc[g.to_index(v)].min(low[g.to_index(u)]);
                    }
                }
            }
            Control::Continue
        });

        bridges
    } else {
        Vec::new()
    }
}

pub fn has_at_least_one_bridge<G>(g: G) -> bool
where
    G: IntoNeighbors + Visitable + IntoNodeIdentifiers + NodeIndexable,
    G::NodeId: std::fmt::Debug,
{
    let mut parent = vec![None; g.node_bound()];
    let mut disc = vec![0; g.node_bound()];
    let mut low = vec![0; g.node_bound()];
    
    if let Some(start) = g.node_identifiers().next() {
        let mut bridges = false;
        depth_first_search(&g, Some(start), |event| -> Control<()> {
            match event {
                DfsEvent::TreeEdge(u, v) => {
                    parent[g.to_index(v)] = Some(u);
                }
                DfsEvent::Discover(u, time) => {
                    low[g.to_index(u)] = time.0;
                    disc[g.to_index(u)] = time.0;
                }
                DfsEvent::Finish(v, _) => {
                    if let Some(u) = parent[g.to_index(v)] {
                        low[g.to_index(u)] = low[g.to_index(v)].min(low[g.to_index(u)]);

                        if low[g.to_index(v)] > disc[g.to_index(u)] {
                            bridges = true;
                            return Control::Break(())
                        }
                    }
                }
                DfsEvent::BackEdge(u, v) | DfsEvent::CrossForwardEdge(u, v) => {
                    if parent[g.to_index(u)] != Some(v) {
                        low[g.to_index(u)] = disc[g.to_index(v)].min(low[g.to_index(u)]);
                    }
                }
            }
            Control::Continue
        });

        bridges
    } else {
        false
    }
}

#[cfg(test)]
mod test_bridge_detection {
    use super::*;
    use petgraph::graph::node_index as n;
    use petgraph::graph::UnGraph;

    #[test]
    fn triangle_has_no_bridge() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0)]);
        assert!(compute_bridges(&g).is_empty());
    }

    #[test]
    fn four_cycle_has_no_bridge() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 3), (3, 0)]);
        assert!(compute_bridges(&g).is_empty());
    }

    #[test]
    fn line_has_bridges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 3)]);
        assert_eq!(
            compute_bridges(&g),
            vec![(n(3), n(2)), (n(2), n(1)), (n(1), n(0))]
        );
    }

    #[test]
    fn tree_has_bridges() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 3), (2, 4), (4, 5), (4, 6)]);
        assert_eq!(
            compute_bridges(&g),
            vec![
                (n(6), n(4)),
                (n(5), n(4)),
                (n(4), n(2)),
                (n(3), n(2)),
                (n(2), n(1)),
                (n(1), n(0))
            ]
        );
    }

    #[test]
    fn one_matching_between_triangles_has_bridges() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3)]);
        assert_eq!(compute_bridges(&g), vec![(n(3), n(2))]);
    }

    #[test]
    fn two_matching_between_triangles_has_no_bridges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[
            (0, 1),
            (1, 2),
            (2, 0),
            (2, 3),
            (1, 4),
            (3, 4),
            (4, 5),
            (5, 3),
        ]);
        assert!(compute_bridges(&g).is_empty());
    }

    #[test]
    fn three_matching_between_triangles_has_no_bridges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[
            (0, 1),
            (1, 2),
            (2, 0),
            (2, 3),
            (1, 4),
            (0, 5),
            (3, 4),
            (4, 5),
            (5, 3),
        ]);
        assert!(compute_bridges(&g).is_empty());
    }
}
