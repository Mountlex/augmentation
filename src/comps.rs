use std::{collections::HashMap, fmt::Display};

use itertools::Itertools;
use num_rational::Rational64;

use crate::{types::Edge, Credit};

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

pub fn c3() -> Component {
    Component::C3([0, 1, 2])
}
pub fn c4() -> Component {
    Component::C4([0, 1, 2, 3])
}
pub fn c5() -> Component {
    Component::C5([0, 1, 2, 3, 4])
}
pub fn c6() -> Component {
    Component::C6([0, 1, 2, 3, 4, 5])
}
pub fn large() -> Component {
    Component::Large(0)
}

pub fn three_cycle() -> ComponentG {
    ComponentG::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 0, EdgeType::Sellable),
    ]))
}

pub fn four_cycle() -> ComponentG {
    ComponentG::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 0, EdgeType::Sellable),
    ]))
}

pub fn five_cycle() -> ComponentG {
    ComponentG::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 4, EdgeType::Sellable),
        (4, 0, EdgeType::Sellable),
    ]))
}
pub fn six_cycle() -> ComponentG {
    ComponentG::Cycle(Graph::from_edges(vec![
        (0, 1, EdgeType::Sellable),
        (1, 2, EdgeType::Sellable),
        (2, 3, EdgeType::Sellable),
        (3, 4, EdgeType::Sellable),
        (4, 5, EdgeType::Sellable),
        (5, 0, EdgeType::Sellable),
    ]))
}

pub fn large_component() -> ComponentG {
    ComponentG::Large(Graph::from_edges(vec![
        (0, 1, EdgeType::Fixed),
        (1, 2, EdgeType::Fixed),
        (0, 2, EdgeType::Fixed),
    ]))
}

pub fn complex_path_component() -> ComponentG {
    ComponentG::Complex(
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

pub fn complex_tree_component() -> ComponentG {
    ComponentG::Complex(
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

pub fn complex_path() -> Component {
    Component::ComplexPath(
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
        [1, 2, 3, 4, 5, 6],
    )
}

pub fn complex_tree() -> Component {
    Component::ComplexTree(
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
        [1, 2, 3, 4, 5, 7, 8],
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
    pub fn components(&self) -> Vec<ComponentG> {
        match self {
            ComponentType::Cycle(l) => vec![ComponentG::Cycle(Graph::from_edges(
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
pub enum ComponentG {
    Cycle(Graph),
    Large(Graph),
    Complex(Complex, Vec<Node>, String),
}

pub enum CompType {
    Cycle(usize),
    Large,
    Complex,
}

#[derive(Clone, Debug)]
pub enum Component {
    C6([Node; 6]),
    C5([Node; 5]),
    C4([Node; 4]),
    C3([Node; 3]),
    Large(Node),
    ComplexPath(Complex, [Node; 6]),
    ComplexTree(Complex, [Node; 7]),
}

impl Component {
    pub fn is_c6(&self) -> bool {
        matches!(self, Component::C6(_))
    }

    pub fn is_c5(&self) -> bool {
        matches!(self, Component::C5(_))
    }

    pub fn is_c4(&self) -> bool {
        matches!(self, Component::C4(_))
    }

    pub fn is_c3(&self) -> bool {
        matches!(self, Component::C3(_))
    }

    pub fn is_complex(&self) -> bool {
        matches!(self, Component::ComplexPath(_, _)) || matches!(self, Component::ComplexTree(_, _))
    }

    pub fn is_large(&self) -> bool {
        matches!(self, Component::Large(_))
    }

    pub fn nodes(&self) -> &[Node] {
        match self {
            Component::C6(nodes) => nodes,
            Component::C5(nodes) => nodes,
            Component::C4(nodes) => nodes,
            Component::C3(nodes) => nodes,
            Component::Large(_) => panic!("large has no known nodes"),
            Component::ComplexPath(_, nodes) => nodes,
            Component::ComplexTree(_, nodes) => nodes,
        }
    }

    pub fn possible_in_out_nodes(&self) -> &[Node] {
        match self {
            Component::C6(nodes) => nodes,
            Component::C5(nodes) => nodes,
            Component::C4(nodes) => nodes,
            Component::C3(nodes) => nodes,
            Component::Large(n) => std::slice::from_ref(n),
            Component::ComplexPath(_, nodes) => nodes,
            Component::ComplexTree(_, nodes) => nodes,
        }
    }

    pub fn is_incident(&self, edge: &Edge) -> bool {
        self.incident(edge).is_some()
    }
    pub fn incident(&self, edge: &Edge) -> Option<Node> {
        if let Component::Large(n) = self {
            if edge.node_incident(n) {
                Some(*n)
            } else {
                None
            }
        } else {
            self.nodes().iter().find(|n| edge.node_incident(n)).cloned()
        }
    }

    pub fn edges(&self) -> Vec<(Node, Node)> {
        match self {
            Component::C6(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C5(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C4(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::C3(nodes) => nodes_to_edges(nodes.as_slice()),
            Component::Large(_nodes) => vec![],
            Component::ComplexPath(complex, _) => complex
                .graph
                .all_edges()
                .map(|(u, v, _)| (u, v))
                .collect_vec(),
            Component::ComplexTree(complex, _) => complex
                .graph
                .all_edges()
                .map(|(u, v, _)| (u, v))
                .collect_vec(),
        }
    }

    pub fn short_name(&self) -> String {
        match self {
            Component::C6(_) => format!("C6"),
            Component::C5(_) => format!("C5"),
            Component::C4(_) => format!("C4"),
            Component::C3(_) => format!("C3"),
            Component::Large(_) => format!("Large"),
            Component::ComplexPath(_, _) => format!("Complex Path"),
            Component::ComplexTree(_, _) => format!("Complex Tree"),
        }
    }

    pub fn fixed_node(&self) -> Node {
        match self {
            Component::C6(nodes) => nodes[0],
            Component::C5(nodes) => nodes[0],
            Component::C4(nodes) => nodes[0],
            Component::C3(nodes) => nodes[0],
            Component::Large(node) => *node,
            Component::ComplexPath(_, blacks) => blacks[3],
            Component::ComplexTree(_, blacks) => blacks[3],
        }
    }

    pub fn is_adjacent(&self, v1: &Node, v2: &Node) -> bool {
        //assert!(self.graph().contains_node(v1));
        //assert!(self.graph().contains_node(v2));
        match self {
            Component::C6(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C5(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C4(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::C3(nodes) => is_adjacent_in_cycle(nodes, v1, v2),
            Component::Large(_) => false,
            Component::ComplexPath(complex, _) => complex.graph.neighbors(*v1).contains(&v2),
            Component::ComplexTree(complex, _) => complex.graph.neighbors(*v1).contains(&v2),
        }
    }

    pub fn graph(&self) -> Graph {
        match self {
            Component::C6(_) | Component::C5(_) | Component::C4(_) | Component::C3(_) => {
                Graph::from_edges(
                    self.edges()
                        .into_iter()
                        .map(|(u, v)| (u, v, EdgeType::Sellable))
                        .collect_vec(),
                )
            }
            Component::Large(n) => {
                let mut g = Graph::new();
                g.add_node(*n);
                g
            }
            Component::ComplexPath(c, _) => c.graph.clone(),
            Component::ComplexTree(c, _) => c.graph.clone(),
        }
    }

    pub fn comp_type(&self) -> CompType {
        match self {
            Component::C6(nodes) => CompType::Cycle(nodes.len()),
            Component::C5(nodes) => CompType::Cycle(nodes.len()),
            Component::C4(nodes) => CompType::Cycle(nodes.len()),
            Component::C3(nodes) => CompType::Cycle(nodes.len()),
            Component::Large(_) => CompType::Large,
            Component::ComplexPath(_, _) => CompType::Complex,
            Component::ComplexTree(_, _) => CompType::Complex,
        }
    }

    pub fn matching_permutations(&self, size: usize) -> Vec<Vec<Node>> {
        match self {
            Component::Large(n) => vec![vec![*n; size]],
            Component::ComplexTree(_, nodes) => nodes.iter().cloned().permutations(size).collect(),
            Component::ComplexPath(_, nodes) => nodes.iter().cloned().permutations(size).collect(),
            _ => self
                .nodes()
                .to_vec()
                .into_iter()
                .permutations(size)
                .collect(),
        }
    }

    pub fn matching_nodes(&self) -> &[Node] {
        match self {
            Component::Large(nodes) => panic!("Large has no matching nodes"),
            Component::ComplexTree(_, nodes) => nodes,
            Component::ComplexPath(_, nodes) => nodes,
            _ => self.nodes(),
        }
    }

    pub fn contains(&self, node: &Node) -> bool {
        if let Component::Large(n) = self {
            n == node
        } else {
            self.nodes().contains(node)
        }
    }
}

fn is_adjacent_in_cycle(nodes: &[Node], v1: &Node, v2: &Node) -> bool {
    // Assumes that nodes are numbered sequentially from nodes[0],...,nodes[k]

    v1.max(v2) - v1.min(v2) == 1
        || (nodes.first() == Some(v1) && nodes.last() == Some(v2))
        || (nodes.first() == Some(v2) && nodes.last() == Some(v1))
}

fn nodes_to_edges(nodes: &[Node]) -> Vec<(Node, Node)> {
    vec![nodes, &[nodes[0]]]
        .concat()
        .windows(2)
        .map(|w| (w[0], w[1]))
        .collect_vec()
}

impl Display for Component {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Component::C6(nodes) => write!(f, "C6 [{}]", nodes.into_iter().join("-")),
            Component::C5(nodes) => write!(f, "C5 [{}]", nodes.into_iter().join("-")),
            Component::C4(nodes) => write!(f, "C4 [{}]", nodes.into_iter().join("-")),
            Component::C3(nodes) => write!(f, "C3 [{}]", nodes.into_iter().join("-")),
            Component::Large(n) => write!(f, "Large [{}]", n),
            Component::ComplexPath(_, _) => write!(f, "Complex Path"),
            Component::ComplexTree(_, _) => write!(f, "Complex Tree"),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Complex {
    pub graph: Graph,
    pub total_black_deg: usize,
    pub num_blocks: usize,
}

impl ComponentG {
    pub fn is_c6(&self) -> bool {
        matches!(self, ComponentG::Cycle(graph) if graph.edge_count() == 6)
    }

    pub fn is_c5(&self) -> bool {
        matches!(self, ComponentG::Cycle(graph) if graph.edge_count() == 5)
    }

    pub fn is_c4(&self) -> bool {
        matches!(self, ComponentG::Cycle(graph) if graph.edge_count() == 4)
    }

    pub fn is_c3(&self) -> bool {
        matches!(self, ComponentG::Cycle(graph) if graph.edge_count() == 3)
    }

    pub fn is_complex(&self) -> bool {
        matches!(self, ComponentG::Complex(_, _, _))
    }

    pub fn is_large(&self) -> bool {
        matches!(self, ComponentG::Large(_))
    }

    pub fn short_name(&self) -> String {
        match self {
            ComponentG::Cycle(g) => format!("C{}", g.edge_count()),
            ComponentG::Large(_) => format!("large"),
            ComponentG::Complex(_, _, name) => name.clone(),
        }
    }

    pub fn matching_sets(&self) -> Vec<Vec<Node>> {
        match self {
            ComponentG::Cycle(g) => g.nodes().powerset().filter(|p| p.len() == 3).collect(),
            ComponentG::Large(g) => vec![g.nodes().collect()],
            ComponentG::Complex(_, nodes, _) => nodes
                .iter()
                .cloned()
                .powerset()
                .filter(|p| p.len() == 3)
                .collect(),
        }
    }

    pub fn fixed_node(&self) -> Node {
        match self {
            ComponentG::Cycle(c) => c.nodes().find(|_| true).unwrap(),
            ComponentG::Large(c) => c.nodes().find(|_| true).unwrap(),
            ComponentG::Complex(_, blacks, _) => blacks[3],
        }
    }

    pub fn matching_permutations(&self, size: usize) -> Vec<Vec<Node>> {
        match self {
            ComponentG::Cycle(g) => g.nodes().permutations(size).collect(),
            ComponentG::Large(g) => vec![g.nodes().take(size).collect()],
            ComponentG::Complex(_, nodes, _) => nodes.iter().cloned().permutations(size).collect(),
        }
    }

    pub fn graph(&self) -> &Graph {
        match self {
            ComponentG::Cycle(g) => g,
            ComponentG::Large(g) => g,
            ComponentG::Complex(c, _, _) => &c.graph,
        }
    }

    pub fn update_graph(&mut self, update: Graph, mapping: HashMap<u32, u32>) {
        match self {
            ComponentG::Cycle(g) | ComponentG::Large(g) => *g = update,
            ComponentG::Complex(c, nodes, _) => {
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
            ComponentG::Cycle(g) => g,
            ComponentG::Large(g) => g,
            ComponentG::Complex(c, _, _) => c.graph,
        }
    }

    pub fn is_adjacent(&self, v1: Node, v2: Node) -> bool {
        assert!(self.graph().contains_node(v1));
        //assert!(self.graph().contains_node(v2));
        match self {
            ComponentG::Cycle(graph) => graph.neighbors(v1).contains(&v2),
            ComponentG::Complex(complex, _black, _) => complex.graph.neighbors(v1).contains(&v2),
            _ => false,
        }
    }
}

impl Display for ComponentG {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ComponentG::Large(_) => write!(f, "Large"),
            ComponentG::Complex(_, _, name) => write!(f, "{}", name),
            ComponentG::Cycle(graph) => write!(
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
    mut others: Vec<ComponentG>,
) -> (Graph, Vec<ComponentG>) {
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

#[derive(Clone, Debug)]
pub struct CreditInv {
    pub c: Rational64,
}

impl CreditInv {
    pub fn new(c: Rational64) -> Self {
        CreditInv { c }
    }
}

impl CreditInv {
    pub fn two_ec_credit(&self, num_edges: usize) -> Credit {
        (self.c * Credit::from_integer(num_edges as i64)).min(self.large())
    }

    pub fn complex_comp(&self) -> Credit {
        (Credit::from_integer(13) * self.c) - Credit::from_integer(2)
    }

    pub fn complex_black(&self, deg: i64) -> Credit {
        Credit::from_integer(deg) * self.c * Credit::new(1, 2)
    }

    pub fn complex_block(&self) -> Credit {
        Credit::from_integer(1)
    }

    pub fn large(&self) -> Credit {
        Credit::from_integer(2)
    }

    pub fn credits(&self, comp: &Component) -> Credit {
        match comp {
            Component::C6(_) => self.two_ec_credit(6),
            Component::C5(_) => self.two_ec_credit(5),
            Component::C4(_) => self.two_ec_credit(4),
            Component::C3(_) => self.two_ec_credit(3),
            Component::Large(_) => self.large(),
            Component::ComplexPath(c, _) => self.complex(c),
            Component::ComplexTree(c, _) => self.complex(c),
        }
    }

    pub fn complex(&self, complex: &Complex) -> Credit {
        self.complex_comp()
            + Credit::from_integer(complex.num_blocks as i64) * self.complex_block()
            + self.complex_black(complex.total_black_deg as i64)
    }
}

impl Display for CreditInv {
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
