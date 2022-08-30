use std::hash::Hash;

use itertools::Itertools;
use petgraph::visit::{
    depth_first_search, Control, Dfs, DfsEvent, EdgeCount, GraphRef, IntoNeighbors,
    IntoNodeIdentifiers, NodeCount, NodeIndexable, Visitable,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComplexCheckResult<G>
where
    G: NodeIndexable,
{
    Complex(Vec<(G::NodeId, G::NodeId)>, Vec<G::NodeId>),
    NoBridges,
    BlackLeaf,
    NotConnected,
    Empty,
}

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

pub fn is_complex<G>(g: G) -> ComplexCheckResult<G>
where
    G: IntoNeighbors + Visitable + IntoNodeIdentifiers + NodeIndexable + NodeCount,
    G::NodeId: std::fmt::Debug + Eq + Hash,
{
    let mut parent = vec![None; g.node_bound()];
    let mut disc = vec![0; g.node_bound()];
    let mut low = vec![0; g.node_bound()];
    let mut bridges = vec![];
    let mut node_count = 0;

    if let Some(start) = g.node_identifiers().next() {
        depth_first_search(&g, Some(start), |event| -> Control<()> {
            match event {
                DfsEvent::TreeEdge(u, v) => {
                    parent[g.to_index(v)] = Some(u);
                }
                DfsEvent::Discover(u, time) => {
                    node_count += 1;
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

        if node_count != g.node_count() {
            // graph not connected!
            return ComplexCheckResult::NotConnected;
        }

        if bridges.is_empty() {
            return ComplexCheckResult::NoBridges;
        }

        let black_vertices: Vec<G::NodeId> = bridges
            .iter()
            .flat_map(|(u, v)| vec![u, v])
            .unique()
            .filter(|&&v| {
                g.neighbors(v)
                    .all(|u| bridges.contains(&(v, u)) || bridges.contains(&(u, v)))
            })
            .cloned()
            .collect();

        if black_vertices.iter().any(|&v| g.neighbors(v).count() == 1) {
            return ComplexCheckResult::BlackLeaf;
        }

        ComplexCheckResult::Complex(bridges, black_vertices)
    } else {
        ComplexCheckResult::Empty
    }
}

pub fn no_bridges_and_connected<G>(g: G) -> bool
where
    G: IntoNeighbors + Visitable + IntoNodeIdentifiers + NodeIndexable + NodeCount,
    G::NodeId: std::fmt::Debug,
{
    let mut parent = vec![None; g.node_bound()];
    let mut disc = vec![0; g.node_bound()];
    let mut low = vec![0; g.node_bound()];
    let mut node_count = 0;

    if let Some(start) = g.node_identifiers().next() {
        let mut bridges = false;
        depth_first_search(&g, Some(start), |event| -> Control<()> {
            match event {
                DfsEvent::TreeEdge(u, v) => {
                    parent[g.to_index(v)] = Some(u);
                }
                DfsEvent::Discover(u, time) => {
                    node_count += 1;
                    low[g.to_index(u)] = time.0;
                    disc[g.to_index(u)] = time.0;
                }
                DfsEvent::Finish(v, _) => {
                    if let Some(u) = parent[g.to_index(v)] {
                        low[g.to_index(u)] = low[g.to_index(v)].min(low[g.to_index(u)]);

                        if low[g.to_index(v)] > disc[g.to_index(u)] {
                            bridges = true;
                            return Control::Break(());
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

        !bridges && node_count == g.node_count()
    } else {
        true
    }
}

fn is_connected<G>(graph: G) -> bool
where
    G: GraphRef + Visitable + IntoNodeIdentifiers + IntoNeighbors + NodeCount + EdgeCount,
{
    if let Some(start) = graph.node_identifiers().next() {
        if graph.edge_count() + 1 < graph.node_count() {
            return false;
        }

        let mut count = 0;
        let mut dfs = Dfs::new(&graph, start);
        while let Some(_nx) = dfs.next(&graph) {
            count += 1;
        }
        count == graph.node_count()
    } else {
        true
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
                            return Control::Break(());
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
mod test_connected {
    use petgraph::prelude::UnGraph;

    use super::*;

    #[test]
    fn triangle() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0)]);
        assert!(is_connected(&g));
    }

    #[test]
    fn parallel_edges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (2, 3)]);
        assert!(!is_connected(&g));
    }

    #[test]
    fn two_triangles() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]);
        assert!(!is_connected(&g));
    }
}

#[cfg(test)]
mod test_complex {
    use petgraph::graph::node_index as n;
    use petgraph::prelude::UnGraph;

    use crate::comps::ComponentType;

    use super::*;

    #[test]
    fn test_complex_base() {
        let graphs = ComponentType::Complex.components();
        let res0 = is_complex(graphs[0].graph());
        let res1 = is_complex(graphs[1].graph());
        assert!(matches!(res0, ComplexCheckResult::Complex(_, _)));
        dbg!(&res1);
        assert!(matches!(res1, ComplexCheckResult::Complex(_, _)));
    }

    #[test]
    fn test_complex_triangle() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0)]);
        assert!(matches!(is_complex(&g), ComplexCheckResult::NoBridges));
    }

    #[test]
    fn test_complex_two_edges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (2, 3)]);
        assert!(matches!(is_complex(&g), ComplexCheckResult::NotConnected));
    }

    #[test]
    fn test_complex_two_triangles() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]);
        assert!(matches!(is_complex(&g), ComplexCheckResult::Complex(_, _)));
        if let ComplexCheckResult::Complex(bridges, blacks) = is_complex(&g) {
            assert_eq!(bridges, vec![(n(3), n(2))]);
            assert_eq!(blacks, vec![])
        }
    }

    #[test]
    fn test_complex_three_triangles() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[
            (0, 1),
            (1, 2),
            (2, 0),
            (3, 4),
            (4, 5),
            (5, 3),
            (6, 7),
            (7, 8),
            (8, 6),
            (9, 0),
            (9, 3),
            (9, 6),
        ]);
        assert!(matches!(is_complex(&g), ComplexCheckResult::Complex(_, _)));
        if let ComplexCheckResult::Complex(bridges, blacks) = is_complex(&g) {
            assert_eq!(bridges, vec![(n(6), n(9)), (n(3), n(9)), (n(9), n(0))]);
            assert_eq!(blacks, vec![n(9)])
        }
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
