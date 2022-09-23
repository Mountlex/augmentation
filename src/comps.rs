use std::{collections::HashMap, fmt::Display};

use itertools::Itertools;
use num_rational::Rational64;

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

pub fn complex_path_component() -> Component {
    Component::Complex(
        Complex {
            graph: Graph::from_edges(vec![
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
            num_blocks: 2,
            total_black_deg: 12,
        },
        vec![1, 2, 3, 4, 5, 6],
        "Complex-Path".into(),
    )
}

pub fn complex_tree_component() -> Component {
    Component::Complex(
        Complex {
            ///          {0,10,11}
            ///          |
            ///          1
            ///          |
            ///          2
            ///          |
            ///          3 -- 7 -- 8 -- {9,12,13}
            ///          |
            ///          4
            ///          |
            ///          5
            ///          |
            ///          {6,14,15}
            graph: Graph::from_edges(vec![
                (0, 10, EdgeType::Fixed),
                (10, 11, EdgeType::Fixed),
                (11, 0, EdgeType::Fixed),
                (0, 1, EdgeType::Sellable),
                (1, 2, EdgeType::Sellable),
                (2, 3, EdgeType::Sellable),
                (3, 4, EdgeType::Sellable),
                (4, 5, EdgeType::Sellable),
                (3, 7, EdgeType::Sellable),
                (7, 8, EdgeType::Sellable),
                (5, 6, EdgeType::Fixed),
                (6, 14, EdgeType::Fixed),
                (14, 15, EdgeType::Fixed),
                (15, 6, EdgeType::Fixed),
                (8, 9, EdgeType::Fixed),
                (9, 12, EdgeType::Fixed),
                (12, 13, EdgeType::Fixed),
                (13, 9, EdgeType::Fixed),
            ]),
            num_blocks: 3,
            total_black_deg: 15,
        },
        vec![1, 2, 3, 4, 5, 7, 8],
        "Complex-Tree".into(),
    )
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
            ComponentType::Large => vec![large_component()],
            ComponentType::Complex => vec![complex_path_component(), complex_tree_component()],
        }
    }
}

#[derive(Clone, Debug)]
pub enum Component {
    Cycle(Graph),
    Large(Graph),
    Complex(Complex, Vec<Node>, String),
}

#[derive(Clone, Debug)]
pub struct Complex {
    pub graph: Graph,
    pub total_black_deg: usize,
    pub num_blocks: usize,
}

impl Component {
    pub fn is_c6(&self) -> bool {
        matches!(self, Component::Cycle(graph) if graph.edge_count() == 6)
    }

    pub fn is_c5(&self) -> bool {
        matches!(self, Component::Cycle(graph) if graph.edge_count() == 5)
    }

    pub fn is_c4(&self) -> bool {
        matches!(self, Component::Cycle(graph) if graph.edge_count() == 4)
    }

    pub fn is_c3(&self) -> bool {
        matches!(self, Component::Cycle(graph) if graph.edge_count() == 3)
    }

    pub fn is_complex(&self) -> bool {
        matches!(self, Component::Complex(_, _, _))
    }

    pub fn is_large(&self) -> bool {
        matches!(self, Component::Large(_))
    }

    pub fn short_name(&self) -> String {
        match self {
            Component::Cycle(g) => format!("C{}", g.edge_count()),
            Component::Large(_) => format!("large"),
            Component::Complex(_, _, name) => name.clone(),
        }
    }

    pub fn matching_sets(&self) -> Vec<Vec<Node>> {
        match self {
            Component::Cycle(g) => g.nodes().powerset().filter(|p| p.len() == 3).collect(),
            Component::Large(g) => vec![g.nodes().collect()],
            Component::Complex(_, nodes, _) => nodes
                .iter()
                .cloned()
                .powerset()
                .filter(|p| p.len() == 3)
                .collect(),
        }
    }

    pub fn fixed_node(&self) -> Node {
        match self {
            Component::Cycle(c) => c.nodes().find(|_| true).unwrap(),
            Component::Large(c) => c.nodes().find(|_| true).unwrap(),
            Component::Complex(_, blacks, _) => blacks[3],
        }
    }

    pub fn matching_permutations(&self, size: usize) -> Vec<Vec<Node>> {
        match self {
            Component::Cycle(g) => g.nodes().permutations(size).collect(),
            Component::Large(g) => vec![g.nodes().take(size).collect()],
            Component::Complex(_, nodes, _) => nodes.iter().cloned().permutations(size).collect(),
        }
    }

    pub fn graph(&self) -> &Graph {
        match self {
            Component::Cycle(g) => g,
            Component::Large(g) => g,
            Component::Complex(c, _, _) => &c.graph,
        }
    }

    pub fn update_graph(&mut self, update: Graph, mapping: HashMap<u32, u32>) {
        match self {
            Component::Cycle(g) | Component::Large(g) => *g = update,
            Component::Complex(c, nodes, _) => {
                c.graph = update;
                nodes.iter_mut().for_each(|b| *b = mapping[b]);
            }
        }
    }

    pub fn nodes(&self) -> Vec<Node> {
        self.graph().nodes().collect_vec()
    }

    pub fn edges(&self) -> Vec<(Node, Node)> {
        self.graph()
            .all_edges()
            .map(|(u, v, _)| (u, v))
            .collect_vec()
    }

    pub fn to_graph(self) -> Graph {
        match self {
            Component::Cycle(g) => g,
            Component::Large(g) => g,
            Component::Complex(c, _, _) => c.graph,
        }
    }

    pub fn is_adjacent(&self, v1: Node, v2: Node) -> bool {
        assert!(self.graph().contains_node(v1));
        //assert!(self.graph().contains_node(v2));
        match self {
            Component::Cycle(graph) => graph.neighbors(v1).contains(&v2),
            Component::Complex(complex, black, _) => complex.graph.neighbors(v1).contains(&v2),
            _ => false,
        }
    }
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::Large(_) => write!(f, "Large"),
            Component::Complex(_, _, name) => write!(f, "{}", name),
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
                let w1_new = nodes.iter().position(|n| n == &w1).unwrap() as u32 + offset;
                let w2_new = nodes.iter().position(|n| n == &w2).unwrap() as u32 + offset;
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

pub trait CreditInvariant: Clone + Display {
    fn credits(&self, comp: &Component) -> Credit {
        match comp {
            Component::Complex(c, _, _) => self.complex(c),

            Component::Large(_) => self.large(),
            Component::Cycle(graph) => self.simple(graph),
        }
    }

    fn two_ec_credit(&self, num_edges: usize) -> Credit;

    fn simple(&self, graph: &Graph) -> Credit {
        self.two_ec_credit(graph.edge_count())
    }
    fn complex(&self, complex: &Complex) -> Credit {
        self.complex_comp()
            + Credit::from_integer(complex.num_blocks as i64) * self.complex_block()
            + self.complex_black(complex.total_black_deg as i64)
    }
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
    fn two_ec_credit(&self, num_edges: usize) -> Credit {
        (self.c * Credit::from_integer(num_edges as i64)).min(self.large())
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

impl Display for DefaultCredits {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Credit Scheme with c = {}", self.c)
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
