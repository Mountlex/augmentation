use std::hash::Hash;

use itertools::Itertools;
use petgraph::visit::{
    depth_first_search, Control, DfsEvent, IntoNeighbors, IntoNodeIdentifiers, NodeCount,
    NodeIndexable, Visitable,
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

impl  <G> ComplexCheckResult<G> where G: NodeIndexable {
    pub fn has_bridges(&self) -> bool {
        matches!(self, ComplexCheckResult::Complex(_, _))
    }
}

#[allow(dead_code)]
pub fn is_complex_slow<G>(g: G, white_vertices: &[G::NodeId]) -> ComplexCheckResult<G>
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
            .filter(|v| !white_vertices.contains(v))
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

struct Frame {
    v: usize,
    p: Option<usize>,
    i: usize,
}

impl Frame {
    fn new(v: usize, p: Option<usize>, i: usize) -> Self {
        Self { v, p, i }
    }
}

//https://stackoverflow.com/questions/23179579/finding-bridges-in-graph-without-recursion

pub fn is_complex<G>(g: G, white_vertices: &[G::NodeId], any_bridge_sc: bool) -> ComplexCheckResult<G>
where
    G: IntoNeighbors + Visitable + IntoNodeIdentifiers + NodeIndexable + NodeCount,
    G::NodeId: std::fmt::Debug + Eq + Hash,
{
    let mut stack: Vec<Frame> = Vec::new();
    let mut enter = vec![0; g.node_bound()];
    let mut ret = vec![0; g.node_bound()];
    let mut used = vec![false; g.node_bound()];
    let mut time = 0;
    let mut bridges = vec![];
    let mut node_count = 0;

    if let Some(start) = g.node_identifiers().next() {
        stack.push(Frame::new(g.to_index(start), None, 0));
    } else {
        return ComplexCheckResult::Empty;
    }

    let mut neighbors = vec![Vec::new(); g.node_bound()];
    neighbors
        .iter_mut()
        .enumerate()
        .for_each(|(n, neigbs)| *neigbs = g.neighbors(g.from_index(n)).collect_vec());

    while let Some(top) = stack.pop() {
        let i = top.i;
        let v = top.v;
        let p = top.p;
        if i == 0 {
            node_count += 1;
            enter[v] = time;
            ret[v] = time;
            time += 1;
            used[v] = true;
        }

        let v_nodeid = g.from_index(v);
        // First part works befor DFS call
        let v_neighbors = neighbors[v].as_slice();

        if i < v_neighbors.len() {
            let to = v_neighbors[i];
            let to_idx = g.to_index(to);
            stack.push(Frame::new(v, p, i + 1));
            if Some(to_idx) != p {
                if used[to_idx] {
                    ret[v] = ret[v].min(enter[to_idx])
                } else {
                    stack.push(Frame::new(to_idx, Some(v), 0));
                }
            }
        }

        if i > 0 && i <= v_neighbors.len() {
            let to = v_neighbors[i - 1]
            ;
            let to_idx = g.to_index(to);
            if Some(to_idx) != p {
                ret[v] = ret[v].min(ret[to_idx]);
                if ret[to_idx] > enter[v] {
                    if any_bridge_sc {
                        return ComplexCheckResult::Complex(vec![], vec![]);
                    }
                    bridges.push((v_nodeid, to));
                }
            }
        }
    }

    if node_count != g.node_count() {
        // graph not connected!
        return ComplexCheckResult::NotConnected;
    }

    if bridges.is_empty() || any_bridge_sc {
        return ComplexCheckResult::NoBridges;
    }

    let black_vertices: Vec<G::NodeId> = bridges
        .iter()
        .flat_map(|(u, v)| vec![u, v])
        .unique()
        .filter(|v| !white_vertices.contains(v))
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
}

// #[cfg(test)]
// mod test_connected {
//     use petgraph::prelude::UnGraph;

//     use super::*;

//     #[test]
//     fn triangle() {
//         let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0)]);
//         assert!(is_connected(&g));
//     }

//     #[test]
//     fn parallel_edges() {
//         let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (2, 3)]);
//         assert!(!is_connected(&g));
//     }

//     #[test]
//     fn two_triangles() {
//         let g: UnGraph<(), ()> =
//             UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3)]);
//         assert!(!is_connected(&g));
//     }
// }

#[cfg(test)]
mod test_complex {
    use petgraph::graph::node_index as n;
    use petgraph::prelude::UnGraph;

    use super::*;

    // #[test]
    // fn test_complex_base() {
    //     let graphs = ComponentType::Complex.components();
    //     let res0 = is_complex(graphs[0].graph());
    //     let res1 = is_complex(graphs[1].graph());
    //     assert!(matches!(res0, ComplexCheckResult::Complex(_, _)));
    //     dbg!(&res1);
    //     assert!(matches!(res1, ComplexCheckResult::Complex(_, _)));
    // }

    #[test]
    fn test_complex_triangle() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0)]);
        assert!(matches!(
            is_complex(&g, &vec![], false),
            ComplexCheckResult::NoBridges
        ));
    }

    #[test]
    fn test_complex_two_edges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (2, 3)]);
        assert!(matches!(
            is_complex(&g, &vec![], false),
            ComplexCheckResult::NotConnected
        ));
    }

    #[test]
    fn test_complex_two_triangles() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0), (3, 4), (4, 5), (5, 3), (2, 3)]);
        assert!(matches!(
            is_complex(&g, &vec![], false),
            ComplexCheckResult::Complex(_, _)
        ));
        if let ComplexCheckResult::Complex(bridges, blacks) = is_complex(&g, &vec![], false) {
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
        assert!(matches!(
            is_complex(&g, &vec![], false),
            ComplexCheckResult::Complex(_, _)
        ));
        if let ComplexCheckResult::Complex(bridges, blacks) = is_complex(&g, &vec![], false) {
            assert_eq!(bridges, vec![(n(6), n(9)), (n(3), n(9)), (n(9), n(0))]);
            assert_eq!(blacks, vec![n(9)])
        }
    }
}

#[cfg(test)]
mod test_bridge_detection {
    use super::*;
    use petgraph::graph::UnGraph;

    #[test]
    fn triangle_has_no_bridge() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0)]);
        assert!(!is_complex(&g, &vec![], true).has_bridges());
    }

    #[test]
    fn four_cycle_has_no_bridge() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 3), (3, 0)]);
        assert!(!is_complex(&g, &vec![], true).has_bridges());
    }

    #[test]
    fn line_has_bridges() {
        let g: UnGraph<(), ()> = UnGraph::from_edges(&[(0, 1), (1, 2), (2, 3)]);
        assert!(
            is_complex(&g, &vec![], true).has_bridges()
        );
    }

    #[test]
    fn tree_has_bridges() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 3), (2, 4), (4, 5), (4, 6)]);
        assert!(
            is_complex(&g, &vec![], true).has_bridges()
        );
    }

    #[test]
    fn one_matching_between_triangles_has_bridges() {
        let g: UnGraph<(), ()> =
            UnGraph::from_edges(&[(0, 1), (1, 2), (2, 0), (2, 3), (3, 4), (4, 5), (5, 3)]);
        assert!(is_complex(&g, &vec![], true).has_bridges());
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
        assert!(!is_complex(&g, &vec![], true).has_bridges());
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
        assert!(!is_complex(&g, &vec![], true).has_bridges());
    }
}
