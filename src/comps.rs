use std::{collections::HashMap, fmt::Display};

use itertools::Itertools;
use num_rational::Rational64;
use petgraph::{
    algo::connected_components,
    prelude::{GraphMap, UnGraphMap},
    visit::{EdgeFiltered, IntoEdgeReferences, NodeCompactIndexable, NodeFiltered, NodeIndexable},
};

use crate::Credit;

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum EdgeType {
    // Not sellable
    Fixed,
    // sellable
    Sellable,
    // buyable
    Buyable,
}

pub type Node = u32;
pub type Graph = petgraph::graphmap::UnGraphMap<Node, EdgeType>;

pub fn three_cycle() -> Component {
    Component::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 0, EdgeType::Sellable),
    ]))
}

pub fn four_cycle() -> Component {
    Component::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 0, EdgeType::Sellable),
    ]))
}

pub fn five_cycle() -> Component {
    Component::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 4, EdgeType::Sellable),
        (4, 0, EdgeType::Sellable),
    ]))
}
pub fn six_cycle() -> Component {
    Component::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 4, EdgeType::Sellable),
        (4, 5, EdgeType::Sellable),
        (5, 0, EdgeType::Sellable),
    ]))
}

pub fn large_component() -> Component {
    Component::Large(Graph::from_edges(vec![
        (0, 1, EdgeType::Fixed),
        (1, 2, EdgeType::Fixed),
        (0, 2, EdgeType::Fixed),
    ]))
}

#[derive(Clone, Debug)]
pub enum ComponentType {
    Cycle(u8),
    Large,
    Complex,
}

impl Display for ComponentType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComponentType::Large => write!(f, "large"),
            ComponentType::Complex => write!(f, "complex"),
            ComponentType::Cycle(l) => write!(f, "{}c", l),
        }
    }
}

impl ComponentType {
    pub fn components(&self) -> Vec<Component> {
        match self {
            ComponentType::Cycle(l) => vec![Component::Cycle(Graph::from_edges(
                (0..*l)
                    .map(|i| (i as u32, ((i + 1) % l) as u32, EdgeType::Sellable))
                    .collect::<Vec<(u32, u32, EdgeType)>>(),
            ))],
            ComponentType::Large => vec![Component::Large(Graph::from_edges(vec![
                (0, 1, EdgeType::Fixed),
                (1, 2, EdgeType::Fixed),
                (2, 0, EdgeType::Fixed),
            ]))],
            ComponentType::Complex => vec![
                Component::ComplexPath(
                    Graph::from_edges(vec![
                        (0, 1, EdgeType::Fixed),
                        (0, 8, EdgeType::Fixed),
                        (8, 9, EdgeType::Fixed),
                        (9, 0, EdgeType::Fixed),
                        (1, 2, EdgeType::Sellable),
                        (2, 3, EdgeType::Sellable),
                        (3, 4, EdgeType::Sellable),
                        (4, 5, EdgeType::Sellable),
                        (5, 6, EdgeType::Sellable),
                        (6, 7, EdgeType::Fixed),
                        (7, 10, EdgeType::Fixed),
                        (10, 11, EdgeType::Fixed),
                        (11, 7, EdgeType::Fixed),
                    ]),
                    vec![1, 2, 3, 4, 5, 6],
                ),
                Component::ComplexY(
                    Graph::from_edges(vec![
                        (0, 7, EdgeType::Fixed),
                        (7, 8, EdgeType::Fixed),
                        (8, 0, EdgeType::Fixed),
                        (0, 1, EdgeType::Fixed),
                        (1, 2, EdgeType::Fixed),
                        (2, 3, EdgeType::Fixed),
                        (3, 4, EdgeType::Fixed),
                        (4, 9, EdgeType::Fixed),
                        (9, 10, EdgeType::Fixed),
                        (10, 4, EdgeType::Fixed),
                        (2, 5, EdgeType::Fixed),
                        (5, 6, EdgeType::Fixed),
                        (6, 11, EdgeType::Fixed),
                        (11, 12, EdgeType::Fixed),
                        (12, 6, EdgeType::Fixed),
                    ]),
                    vec![1, 2, 3, 5],
                ),
            ],
        }
    }
}

#[derive(Clone, Debug)]
pub enum Component {
    Cycle(Graph),
    Large(Graph),
    ComplexPath(Graph, Vec<u32>),
    ComplexY(Graph, Vec<u32>),
}

pub enum BWNode {
    Black(u32),
    White(u32),
}

pub type BWGraph = UnGraphMap<BWNode, EdgeType>;

impl Component {
    pub fn short_name(&self) -> String {
        match self {
            Component::Large(_) => format!("large"),
            Component::ComplexPath(_, _) => format!("complex-path"),
            Component::ComplexY(_, _) => format!("complex-y"),
            Component::Cycle(graph) => format!("{}c", graph.node_count()),
        }
    }

    pub fn possible_matchings(&self) -> Vec<Vec<u32>> {
        match self {
            Component::Cycle(g) => g.nodes().powerset().filter(|p| p.len() == 3).collect(),
            Component::Large(g) => vec![g.nodes().collect()],
            Component::ComplexPath(g, black) => black
                .clone()
                .into_iter()
                .powerset()
                .filter(|p| p.len() == 3)
                .collect(),
            Component::ComplexY(g, black) => black
                .clone()
                .into_iter()
                .powerset()
                .filter(|p| p.len() == 3)
                .collect(),
        }
    }

    pub fn graph(&self) -> &Graph {
        match self {
            Component::Cycle(g) => g,
            Component::Large(g) => g,
            Component::ComplexPath(g, _) => g,
            Component::ComplexY(g, _) => g,
        }
    }

    pub fn update_graph(&mut self, update: Graph, mapping: HashMap<u32, u32>) {
        match self {
            Component::Cycle(g) | Component::Large(g) => *g = update,
            Component::ComplexPath(g, blacks) | Component::ComplexY(g, blacks) => {
                *g = update;
                blacks.iter_mut().for_each(|b| *b = mapping[b]);
            }
        }
    }

    pub fn to_graph(self) -> Graph {
        match self {
            Component::Cycle(g) => g,
            Component::Large(g) => g,
            Component::ComplexPath(g, _) => g,
            Component::ComplexY(g, _) => g,
        }
    }
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Large(_) => write!(f, "Large"),
            Component::ComplexPath(_, _) => write!(f, "Complex-Path"),
            Component::ComplexY(_, _) => write!(f, "Complex-Y"),
            Component::Cycle(graph) => write!(
                f,
                "{}-Cycle [{}]",
                graph.node_count(),
                graph.nodes().map(|n| format!("{}", n)).join("-")
            ),
        }
    }
}

/// Adds nodes and edges from `others` to `base` and relabels and return node weights of those.
/// The node weights of `base` will not be changed!
///
/// Example:
/// 0 - 1    0 - 1
///  \ /      \ /
///   3        2
/// base      others
///
/// gives
///
/// 0 - 1    4 - 5
///  \ /      \ /
///   3        6
///       base      
///
/// and returns [[4,5,6]]
pub fn merge_graphs_to_base(
    mut base: Graph,
    mut others: Vec<Graph>,
) -> (Graph, Vec<Graph>, Vec<HashMap<u32, u32>>) {
    let mut offset: u32 = if let Some(max) = base.nodes().max() {
        max + 1
    } else {
        0
    };
    let mut mappings = vec![];
    for graph in &mut others {
        let mut mapping = HashMap::new();
        let nodes = graph.nodes().collect::<Vec<Node>>();
        let edges: Vec<(Node, Node, EdgeType)> = graph
            .all_edges()
            .map(|(w1, w2, t)| {
                let w1_new = (nodes.iter().position(|n| n == &w1).unwrap() as u32 + offset);
                let w2_new = (nodes.iter().position(|n| n == &w2).unwrap() as u32 + offset);
                mapping.insert(w1, w1_new);
                mapping.insert(w2, w2_new);
                (w1_new, w2_new, *t)
            })
            .collect();
        base.extend(&edges);
        *graph = Graph::from_edges(edges);
        offset += nodes.len() as u32;
        mappings.push(mapping);
    }

    (base, others, mappings)
}

pub fn merge_components_to_base(
    base: Graph,
    mut others: Vec<Component>,
) -> (Graph, Vec<Component>) {
    let graphs = others.iter().map(|c| c.graph().clone()).collect();
    let (graph, graphs, mappings) = merge_graphs_to_base(base, graphs);
    others
        .iter_mut()
        .zip(graphs)
        .zip(mappings)
        .for_each(|((c, g), m)| c.update_graph(g, m));
    (graph, others)
}

pub fn edges_of_type<'a>(graph: &'a Graph, typ: EdgeType) -> Vec<(Node, Node)> {
    graph
        .all_edges()
        .filter(|(_, _, t)| **t == typ)
        .map(|(a, b, _)| (a, b))
        .collect()
}

pub fn merge_graphs(graphs: Vec<Graph>) -> (Graph, Vec<Graph>) {
    let (g, others, _) = merge_graphs_to_base(Graph::new(), graphs);
    (g, others)
}

// pub struct ComplexStructure<G>
// where
//     G: NodeIndexable,
// {
//     bridges: Vec<(G::NodeId, G::NodeId)>,
//     black_vertices: Vec<G::NodeId>,
//     num_blocks: usize,
// }

pub fn compute_number_of_blocks<G>(
    graph: &Graph,
    bridges: &Vec<(Node, Node)>,
    black_vertices: &Vec<Node>,
) -> usize {
    let blocks_graph = EdgeFiltered::from_fn(graph, |(v, u, _)| {
        !(black_vertices.contains(&v) && !black_vertices.contains(&u))
    });
    let num_blocks = connected_components(&blocks_graph);
    // ComplexStructure {
    //     bridges,
    //     black_vertices,
    //     num_blocks,
    //}
    num_blocks
}

pub trait CreditInvariant: Clone {
    fn credits(&self, comp: &Component) -> Credit {
        match comp {
            Component::ComplexPath(graph, _) => {
                self.complex_comp()
                    + Credit::from_integer(6) * self.complex_black(2)
                    + Credit::from_integer(2) * self.complex_block()
            }

            Component::ComplexY(graph, _) => {
                self.complex_comp()
                    + Credit::from_integer(3) * self.complex_black(2)
                    + self.complex_black(3)
                    + Credit::from_integer(3) * self.complex_block()
            }

            Component::Large(_) => self.large(),
            Component::Cycle(graph) => self.simple(graph),
        }
    }
    fn simple(&self, graph: &Graph) -> Credit;
    fn complex_comp(&self) -> Credit;
    fn complex_black(&self, deg: i64) -> Credit;
    fn complex_block(&self) -> Credit;
    fn large(&self) -> Credit;
}

#[derive(Clone, Debug)]
pub struct DefaultCredits {
    pub c: Rational64,
}

impl DefaultCredits {
    pub fn new(c: Rational64) -> Self {
        DefaultCredits { c }
    }
}

impl CreditInvariant for DefaultCredits {
    fn simple(&self, graph: &Graph) -> Credit {
        self.c * Credit::from_integer(graph.edge_count() as i64)
    }

    fn complex_comp(&self) -> Credit {
        (Credit::from_integer(13) * self.c) - Credit::from_integer(2)
    }

    fn complex_black(&self, deg: i64) -> Credit {
        Credit::from_integer(deg) * self.c * Credit::new(1, 2)
    }

    fn complex_block(&self) -> Credit {
        Credit::from_integer(1)
    }

    fn large(&self) -> Credit {
        Credit::from_integer(2)
    }
}

#[cfg(test)]
mod test_merge {
    use super::*;

    #[test]
    fn test_two_triangles() {
        let base = three_cycle().to_graph();
        let other = three_cycle();
        let (base, comps) = merge_components_to_base(base, vec![other]);

        assert_eq!(base.node_count(), 6);
        assert_eq!(
            comps[0].graph().nodes().collect::<Vec<u32>>(),
            vec![3, 4, 5]
        )
    }

    #[test]
    fn test_three_triangles() {
        let base = three_cycle().to_graph();
        let other1 = three_cycle();
        let other2 = three_cycle();
        let (base, comps) = merge_components_to_base(base, vec![other1, other2]);

        assert_eq!(base.node_count(), 9);
        assert_eq!(
            comps[0].graph().nodes().collect::<Vec<u32>>(),
            vec![3, 4, 5]
        );
        assert_eq!(
            comps[1].graph().nodes().collect::<Vec<u32>>(),
            vec![6, 7, 8]
        );
    }
}
