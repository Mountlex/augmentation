use core::panic;
use std::fmt::Write;
use std::marker::PhantomData;
use std::ops::Range;
use std::slice::Iter;
use std::{collections::HashMap, fmt::Display, path::PathBuf};

use itertools::{iproduct, Itertools};
use petgraph::algo::connected_components;
use petgraph::visit::EdgeFiltered;
use petgraph::{
    algo::matching,
    visit::{depth_first_search, Control, DfsEvent, IntoNeighbors},
};

use crate::bridges::{is_complex, ComplexCheckResult};
use crate::comps::DefaultCredits;
use crate::enumerators::{
    ComponentHitEnumerator, ComponentHitOutput, MatchingHitEnumerator, MatchingHitEnumeratorOutput,
    MatchingNodesEnumerator, NPCEnumOutput, NPCEnumerator, PathEnumerator, PathEnumeratorInput,
};
use crate::proof_tree::Tree;
use crate::tactics::{LocalComplexMerge, LocalMerge, LongerPathTactic};
use crate::{
    comps::{
        merge_components_to_base, merge_graphs, Component, CreditInvariant, EdgeType, Graph, Node,
    },
    edges_of_type,
    local_merge::{find_feasible_merge, prove_via_direct_merge, FeasibleMerge, MergeResult},
    proof_tree::ProofNode,
    Credit,
};

#[derive(Debug, Clone)]
pub struct AbstractNode {
    pub comp: Component,
    pub nice_pair: bool,
    pub used: bool,
}

impl AbstractNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    fn value<C: CreditInvariant>(&self, credit_inv: C, lower_complex: bool) -> Credit {
        let comp_credit_minus_edge = credit_inv.credits(&self.comp) - Credit::from_integer(1);
        let complex = if lower_complex {
            credit_inv.complex_comp()
        } else {
            Credit::from_integer(0)
        };

        if self.nice_pair {
            if self.comp.is_complex() {
                complex + credit_inv.complex_black(4)
            } else {
                comp_credit_minus_edge + Credit::from_integer(1)
            }
        } else {
            if self.comp.is_complex() {
                complex + credit_inv.complex_black(2)
            } else {
                comp_credit_minus_edge
            }
        }
    }
}

impl Display for AbstractNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.nice_pair {
            write!(f, "Abstract Node {} with nice pair", self.comp)
        } else {
            write!(f, "Abstract Node {}", self.comp)
        }
    }
}

#[derive(Debug, Clone)]
pub struct ZoomedNode {
    pub comp: Component,
    pub npc: NicePairConfig,
    pub in_node: Option<Node>,
    pub out_node: Option<Node>,
}

impl ZoomedNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }

    fn value<C: CreditInvariant>(
        &self,
        credit_inv: C,
        lower_complex: bool,
        cycle_in: Node,
        cycle_out: Node,
    ) -> Credit {
        assert!(self.comp.graph().contains_node(cycle_in));
        assert!(self.comp.graph().contains_node(cycle_out));

        let comp_credit_minus_edge = credit_inv.credits(&self.comp) - Credit::from_integer(1);
        let complex = if lower_complex {
            credit_inv.complex_comp()
        } else {
            Credit::from_integer(0)
        };

        if self.npc.is_nice_pair(cycle_in, cycle_out) {
            if self.comp.is_complex() {
                complex
                    + complex_cycle_value_base(
                        credit_inv.clone(),
                        self.comp.graph(),
                        cycle_in,
                        cycle_out,
                    )
            } else {
                comp_credit_minus_edge + Credit::from_integer(1)
            }
        } else {
            if self.comp.is_complex() {
                complex
                    + complex_cycle_value_base(
                        credit_inv.clone(),
                        self.comp.graph(),
                        cycle_in,
                        cycle_out,
                    )
            } else {
                comp_credit_minus_edge
            }
        }
    }
}

impl Display for ZoomedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Node {} with in={:?} and out={:?}",
            self.comp, self.in_node, self.out_node
        )
    }
}

fn complex_cycle_value_base<C: CreditInvariant>(
    credit_inv: C,
    graph: &Graph,
    a: Node,
    b: Node,
) -> Credit {
    let mut predecessor = HashMap::new();
    depth_first_search(&graph, Some(a), |event| {
        if let DfsEvent::TreeEdge(u, v) = event {
            predecessor.insert(v, u);
            if v == b {
                return Control::Break(v);
            }
        }
        Control::Continue
    });

    let mut next = b;
    let mut path = vec![next];
    while next != a {
        let pred = *predecessor.get(&next).unwrap();
        path.push(pred);
        next = pred;
    }
    path.reverse();

    path.into_iter()
        .map(|v| credit_inv.complex_black(graph.neighbors(v).count() as i64))
        .sum()
}

#[derive(Debug, Clone)]
pub enum SuperNode {
    Zoomed(ZoomedNode),
    Abstract(AbstractNode),
}

impl SuperNode {
    pub fn get_comp(&self) -> &Component {
        match self {
            SuperNode::Zoomed(node) => node.get_comp(),
            SuperNode::Abstract(node) => node.get_comp(),
        }
    }
}

impl Display for SuperNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            SuperNode::Zoomed(n) => write!(f, "{}", n),
            SuperNode::Abstract(n) => write!(f, "{}", n),
        }
    }
}

#[derive(Clone, Debug)]
pub struct NicePath {
    pub nodes: Vec<SuperNode>,
    pub graph: Graph,
}

impl Display for NicePath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        write!(
            f,
            "{}",
            self.nodes
                .iter()
                .map(|node| format!("{}", node))
                .join(" -- ")
        )?;
        write!(f, "]")
    }
}

#[derive(Clone, Debug)]
pub struct PseudoCycle {
    nodes: Vec<SuperNode>,
}

impl PseudoCycle {
    fn value<C: CreditInvariant>(&self, credit_inv: C) -> Credit {
        let first_complex = self
            .nodes
            .iter()
            .enumerate()
            .find(|(_, n)| n.get_comp().is_complex())
            .map(|(i, _)| i);

        self.nodes
            .iter()
            .enumerate()
            .map(|(j, node)| {
                let lower_complex = first_complex.is_some() && first_complex.unwrap() < j;

                match node {
                    SuperNode::Abstract(abs) => abs.value(credit_inv.clone(), lower_complex),
                    SuperNode::Zoomed(zoomed) => zoomed.value(
                        credit_inv.clone(),
                        lower_complex,
                        zoomed.in_node.unwrap(),
                        zoomed.out_node.unwrap(),
                    ),
                }
            })
            .sum()
    }
}

impl Display for PseudoCycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        write!(
            f,
            "{}",
            self.nodes
                .iter()
                .map(|node| format!("{}", node))
                .join(" -- ")
        )?;
        write!(f, "]")
    }
}

#[derive(Clone, Debug)]
pub enum PseudoNode {
    Abstract,
    Node(Node),
}

impl Display for PseudoNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PseudoNode::Abstract => write!(f, "AbstractNode"),
            PseudoNode::Node(n) => write!(f, "Real Node {}", n),
        }
    }
}

pub fn prove_nice_path_progress<C: CreditInvariant>(
    comps: Vec<Component>,
    credit_inv: C,
    output_dir: PathBuf,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    for last_comp in &comps {
        let mut path_end_node = ProofNode::new_all(format!(
            "Prove progress for all paths ending with {}",
            last_comp
        ));

        for (c1, c2, c3) in iproduct!(comps.clone(), comps.clone(), comps.clone()) {
            let path = vec![c1, c2, c3, last_comp.clone()];
            let (path_graph, path) = merge_components_to_base(Graph::new(), path);

            let nodes = path
                .into_iter()
                .map(|c| {
                    let nice_pair = match &c {
                        Component::Cycle(cycle) if cycle.edge_count() <= 5 => true,
                        Component::Complex(_, _, _) => true,
                        _ => false,
                    };
                    SuperNode::Abstract(AbstractNode {
                        comp: c,
                        nice_pair,
                        used: false,
                    })
                })
                .collect();

            let nice_path = NicePath {
                nodes,
                graph: path_graph,
            };

            let mut path_node = ProofNode::new_all(format!("Prove nice path {}", nice_path));
            let res = prove_nice_path(nice_path, credit_inv.clone(), &mut path_node);
            path_end_node.add_child(path_node);
            if !res {
                break;
            }
        }

        let proved = path_end_node.eval();

        let filename = if proved {
            log::info!("✔️ Proved nice path progress ending in {}", last_comp);
            output_dir.join(format!("proof_{}.txt", last_comp.short_name()))
        } else {
            log::warn!("❌ Disproved nice path progress ending in {}", last_comp);
            output_dir.join(format!("wrong_proof_{}.txt", last_comp.short_name()))
        };

        let mut buf = String::new();
        writeln!(
            &mut buf,
            "============= Proof with {} ===============",
            credit_inv
        )
        .expect("Unable to write file");
        path_end_node
            .print_tree(&mut buf, 0)
            .expect("Unable to format tree");
        std::fs::write(filename, buf).expect("Unable to write file");
    }
}

pub fn prove_nice_path_progress_new<C: CreditInvariant>(
    comps: Vec<Component>,
    credit_inv: C,
    output_dir: PathBuf,
) {
    std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

    let c = credit_inv.complex_black(2);

    let path_length = 4;

    for last_comp in &comps {
        let mut proof = all(
            PathEnumerator,
            all(
                MatchingHitEnumerator,
                all(
                    NPCEnumerator::new(),
                    or::<NPCEnumOutput<MatchingHitEnumeratorOutput>, _, _>(
                        LongerPathTactic,
                        any(
                            ComponentHitEnumerator,
                            or::<ComponentHitOutput, _, _>(
                                LocalComplexMerge,
                                all(
                                    MatchingNodesEnumerator,
                                    all(NPCEnumerator::new(), LocalMerge),
                                ),
                            ),
                        ),
                    ),
                ),
            ),
        )
        .action(
            PathEnumeratorInput::new(last_comp.clone(), comps.clone()),
            &ProofContext {
                credit_inv: DefaultCredits::new(c),
            },
        );

        let proved = proof.eval();

        let filename = if proved {
            log::info!("✔️ Proved nice path progress ending in {}", last_comp);
            output_dir.join(format!("proof_{}.txt", last_comp.short_name()))
        } else {
            log::warn!("❌ Disproved nice path progress ending in {}", last_comp);
            output_dir.join(format!("wrong_proof_{}.txt", last_comp.short_name()))
        };

        let mut buf = String::new();
        writeln!(
            &mut buf,
            "============= Proof with {} ===============",
            credit_inv
        )
        .expect("Unable to write file");
        proof
            .print_tree(&mut buf, 0)
            .expect("Unable to format tree");
        std::fs::write(filename, buf).expect("Unable to write file");
    }
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct PathMatchingEdge(pub Node, pub PathMatchingHits);

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum PathMatchingHits {
    Path(usize),
    Outside,
}

impl PathMatchingEdge {
    pub fn source(&self) -> Node {
        self.0.clone()
    }

    pub fn hit(&self) -> PathMatchingHits {
        self.1.clone()
    }

    pub fn hits_path(&self) -> Option<usize> {
        match self.1 {
            PathMatchingHits::Path(i) => Some(i),
            PathMatchingHits::Outside => None,
        }
    }

    pub fn hits_outside(&self) -> bool {
        matches!(self.1, PathMatchingHits::Outside)
    }
}

impl Display for PathMatchingEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.1 {
            PathMatchingHits::Path(j) => write!(f, "{} -- path[{}]", self.0, j),
            PathMatchingHits::Outside => write!(f, "{} -- outside", self.0),
        }
    }
}

pub fn get_local_merge_graph(
    comp1: &Component,
    comp2: &Component,
    matching: &Vec<(Node, Node)>,
) -> Graph {
    let mut graph = comp1.graph().clone();
    for (v1, v2, t) in comp2.graph().all_edges() {
        graph.add_edge(v1, v2, *t);
    }
    for (m1, m2) in matching {
        graph.add_edge(*m1, *m2, EdgeType::Buyable);
    }
    graph
}

#[derive(Debug, Clone)]
pub struct NicePairConfig {
    nice_pairs: Vec<(Node, Node)>,
}

impl Display for NicePairConfig {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[ ")?;
        write!(
            f,
            "{}",
            self.nice_pairs
                .iter()
                .map(|(a, b)| format!("({}, {})", a, b))
                .join(", ")
        )?;
        write!(f, " ]")
    }
}

impl NicePairConfig {
    fn empty() -> Self {
        NicePairConfig { nice_pairs: vec![] }
    }

    pub fn is_nice_pair(&self, u: Node, v: Node) -> bool {
        self.nice_pairs
            .iter()
            .find(|(a, b)| (*a == u && *b == v) || (*a == v && *b == u))
            .is_some()
    }
}

fn prove_nice_path_matching<C: CreditInvariant>(
    path: &NicePath,
    credit_inv: C,
    m_path: PathMatchingEdge,
    m1: PathMatchingEdge,
    m2: PathMatchingEdge,
    proof: &mut ProofNode,
) -> bool {
    assert!(m_path.hits_path().is_some());

    let path_len = path.nodes.len();
    let last_comp_ref = path.nodes.last().unwrap().get_comp();
    let mut matching = vec![m_path, m1, m2];
    matching.sort_by_key(|m| m.hit());

    for np_config_last in comp_npcs(
        last_comp_ref,
        &vec![m_path.source(), m1.source(), m2.source()],
    ) {
        let mut case_path = path.clone();
        *case_path.nodes.last_mut().unwrap() = SuperNode::Zoomed(ZoomedNode {
            comp: case_path.nodes.last().unwrap().get_comp().clone(),
            in_node: Some(m_path.source()),
            out_node: None,
            npc: np_config_last.clone(),
        });

        let mut proof_npc = ProofNode::new_any(format!(
            "Proof for nice pairs {:?} of last component",
            np_config_last
        ));

        // Find longer nice path
        if is_longer_nice_path_possible(
            last_comp_ref,
            &np_config_last,
            &m_path,
            &m1,
            &mut proof_npc,
        ) {
            proof.add_child(proof_npc);
            return true;
        }
        if is_longer_nice_path_possible(
            last_comp_ref,
            &np_config_last,
            &m_path,
            &m2,
            &mut proof_npc,
        ) {
            proof.add_child(proof_npc);
            return true;
        }

        // TODO contractability of c5

        // Expand matching hits
        // Now if we land here, one of the matching edges should hit the path
        // check if we can do a local merge using matching edges
        for (num_edges, hit_comp) in matching
            .iter()
            .filter(|m_edge| m_edge.hits_path().is_some())
            .map(|m_edge| m_edge.hit())
            .dedup_with_count()
        {
            if let PathMatchingHits::Path(hit_comp_idx) = hit_comp {
                let right_matched: Vec<Node> = matching
                    .iter()
                    .filter(|m_edge| m_edge.hit() == hit_comp)
                    .map(|m_edge| m_edge.source())
                    .collect();
                assert_eq!(right_matched.len(), num_edges);
                let left_comp = path.nodes[hit_comp_idx].get_comp();

                if num_edges == 1 {
                    let right_match = *right_matched.first().unwrap();
                    // only try complex merges

                    let complex_merge = left_comp.graph().nodes().all(|left_match| {
                        let graph_with_matching = get_local_merge_graph(
                            left_comp,
                            last_comp_ref,
                            &vec![(left_match, right_match)],
                        );

                        prove_via_direct_merge(
                            &graph_with_matching,
                            vec![left_comp, last_comp_ref],
                            credit_inv.clone(),
                            &mut ProofNode::new_any(String::new()),
                        )
                    });

                    if complex_merge {
                        proof_npc.add_child(ProofNode::new_leaf(format!("Complex Merge!"), true));
                        proof.add_child(proof_npc);
                        return true;
                    }
                } else {
                    // two or three matching edges to hit_comp
                    let local_merge_res = left_comp
                        .matching_permutations(right_matched.len())
                        .into_iter()
                        .all(|left_matched| {
                            comp_npcs(&left_comp, &left_matched)
                                .into_iter()
                                .all(|np_config_left| {
                                    if local_merge_possible(
                                        left_comp,
                                        last_comp_ref,
                                        &left_matched,
                                        &right_matched,
                                        &np_config_left,
                                        &np_config_last,
                                        credit_inv.clone(),
                                    ) {
                                        return true;
                                    }

                                    //  TODO Longer path if local merge not possible
                                    if num_edges == 2
                                        && (m1.hits_outside() || m2.hits_outside())
                                        && (m1.hits_path() == Some(path_len - 2)
                                            || m2.hits_path() == Some(path_len - 2))
                                    {
                                        let m_outside = vec![m1, m2]
                                            .into_iter()
                                            .find(|&m| m.hits_outside())
                                            .unwrap();
                                        let (m_path, m_other) =
                                            if right_matched[0] == m_path.source() {
                                                (
                                                    Edge(left_matched[0], right_matched[0]),
                                                    Edge(left_matched[1], right_matched[1]),
                                                )
                                            } else {
                                                (
                                                    Edge(left_matched[1], right_matched[1]),
                                                    Edge(left_matched[0], right_matched[0]),
                                                )
                                            };

                                        if longer_nice_path_via_matching_swap(
                                            left_comp,
                                            &np_config_last,
                                            last_comp_ref,
                                            m_path,
                                            m_other,
                                            m_outside,
                                        ) {
                                            return true;
                                        }
                                    }

                                    return false;
                                })
                        });

                    if local_merge_res {
                        proof_npc.add_child(ProofNode::new_leaf(
                            format!("Local Merge or Longer Path!"),
                            true,
                        ));
                        proof.add_child(proof_npc);
                        return true;
                    }
                }
            }
        }

        // If we land here, we want that at least one matching edge hits C_j for j <= l - 2.
        if !(matches!(m1.hit(), PathMatchingHits::Path(j) if j <= path_len - 3)
            || matches!(m2.hit(), PathMatchingHits::Path(j) if j <= path_len - 3))
        {
            proof_npc.add_child(ProofNode::new_leaf(
                format!("There are no matching edges forming cycles! Aborting"),
                false,
            ));
            proof.add_child(proof_npc);
            return false;
        }

        // Try worst-case merge
        // TODO also good cases and then exclude the rest
        let mut cases_remain: Vec<MergeCases> = vec![];
        for m_edge in vec![m1, m2]
            .into_iter()
            .filter(|m_edge| matches!(m_edge.hit(), PathMatchingHits::Path(r) if r <= path_len - 3))
        {
            if check_nice_path_with_cycle(
                &case_path,
                m_edge,
                false,
                credit_inv.clone(),
                &mut proof_npc,
            ) {
                proof.add_child(proof_npc);
                return true;
            } else if check_nice_path_with_cycle(
                &case_path,
                m_edge,
                true,
                credit_inv.clone(),
                &mut proof_npc,
            ) {
                cases_remain.push(MergeCases::NoNicePair(m_edge))
                // it remains to check merge for non-nice pair hit
            } else {
                cases_remain.push(MergeCases::NoNicePair(m_edge));
                cases_remain.push(MergeCases::NicePair(m_edge));
                // it remains to check merge for nice pair and non-nice pair
            }
        }

        proof_npc.add_child(ProofNode::new_leaf(format!("Tactics exhausted!"), false));
        proof.add_child(proof_npc);
        return false;
    }

    false
}

enum MergeCases {
    NoNicePair(PathMatchingEdge),
    NicePair(PathMatchingEdge),
}

#[derive(Copy, Clone, Debug, Default)]
pub struct Edge(pub Node, pub Node);

impl PartialEq for Edge {
    fn eq(&self, other: &Self) -> bool {
        (self.0 == other.0 && self.1 == other.1) || (self.0 == other.1 && self.1 == other.0)
    }
}

impl Eq for Edge {}

pub fn longer_nice_path_via_matching_swap(
    prelast: &Component,
    last_npc: &NicePairConfig,
    last: &Component,
    m_path: Edge,
    m_other: Edge,
    m_outside: PathMatchingEdge,
) -> bool {
    // If matching edge swap cannot be a nice path
    if (last.is_c3() || last.is_c4() || last.is_c5() || last.is_complex())
        && !last_npc.is_nice_pair(m_other.1, m_outside.source())
    {
        return false;
    }

    // Now if C_l-1 does not care about nice pairs, we are done!
    if prelast.is_c6() || prelast.is_large() {
        return true;
    }

    // For others, we have to check that swaping the path edges keeps a nice pair
    if prelast
        .graph()
        .nodes()
        .filter(|left_in| *left_in != m_path.0)
        .all(|left_in| {
            // for any left_in, we consider all possible hamiltonian paths for the current nice pair
            hamiltonian_paths(left_in, m_path.0, &prelast.nodes())
                .into_iter()
                .all(|ham_path| {
                    let edges = ham_path
                        .windows(2)
                        .map(|e| (e[0], e[1]))
                        .chain(prelast.edges().into_iter())
                        .collect_vec();

                    // If for every such path, a nice pair using _any_ hamiltonian path for left_in and the new path edge endpoint is possible, it must be a nice pair
                    hamiltonian_paths(left_in, m_other.0, &prelast.nodes())
                        .into_iter()
                        .any(|path| {
                            path.windows(2)
                                .map(|e| (e[0], e[1]))
                                .all(|(u, v)| edges.contains(&(u, v)) || edges.contains(&(v, u)))
                        })
                })
        })
    {
        return true;
    }

    return false;
}

fn hamiltonian_paths(v1: Node, v2: Node, nodes: &Vec<Node>) -> Vec<Vec<Node>> {
    assert!(nodes.contains(&v1));
    assert!(nodes.contains(&v2));

    nodes
        .iter()
        .cloned()
        .filter(|v| v != &v1 && v != &v2)
        .permutations(nodes.len() - 2)
        .map(|middle| vec![vec![v1], middle, vec![v2]].concat())
        .collect_vec()
}

pub fn comp_npcs(comp: &Component, nodes: &Vec<Node>) -> Vec<NicePairConfig> {
    match comp {
        Component::Cycle(c) if c.edge_count() <= 5 => {
            let all_pairs = nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .collect_vec();
            let adj_pairs: Vec<(u32, u32)> = all_pairs
                .iter()
                .filter(|(u, v)| comp.is_adjacent(*u, *v))
                .cloned()
                .collect();
            all_pairs
                .into_iter()
                .powerset()
                .filter(|config| {
                    // if config misses a nice pair although it is a pair of adjacent vertices, remove it
                    adj_pairs
                        .iter()
                        .all(|(u, v)| config.contains(&(*u, *v)) || config.contains(&(*v, *u)))
                })
                .map(|config| NicePairConfig { nice_pairs: config })
                .collect_vec()
        }
        Component::Cycle(c) => vec![NicePairConfig {
            nice_pairs: c.all_edges().map(|(u, v, t)| (u, v)).collect_vec(),
        }],
        Component::Large(_) => vec![NicePairConfig::empty()],
        Component::Complex(_, black, _) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(&v2))
                .collect_vec(),
        }],
    }
}

fn local_merge_possible<C: CreditInvariant>(
    left_comp: &Component,
    right_comp: &Component,
    left_matched: &Vec<u32>,
    right_matched: &Vec<u32>,
    np_config_left: &NicePairConfig,
    np_config_right: &NicePairConfig,
    credit_inv: C,
) -> bool {
    let matching = left_matched
        .into_iter()
        .zip(right_matched.iter())
        .map(|(l, r)| (*l, *r))
        .collect_vec();
    let graph_with_matching = get_local_merge_graph(left_comp, right_comp, &matching);

    let total_comp_credit = credit_inv.credits(left_comp) + credit_inv.credits(right_comp);

    if left_comp.is_complex() || right_comp.is_complex() {
        for sell in edges_of_type(&graph_with_matching, EdgeType::Sellable)
            .into_iter()
            .powerset()
        {
            let sell_credits = Credit::from_integer(sell.len() as i64);
            let mut total_plus_sell = total_comp_credit + sell_credits;

            for buy in matching
                .iter()
                .cloned()
                .powerset()
                .filter(|p| !p.is_empty())
            {
                let buy_credits = Credit::from_integer(buy.len() as i64);

                let check_graph = EdgeFiltered::from_fn(&graph_with_matching, |(v1, v2, t)| {
                    if t == &EdgeType::Sellable && sell.contains(&(v1, v2))
                        || sell.contains(&(v2, v1))
                    {
                        false
                    } else if t == &EdgeType::Buyable
                        && !buy.contains(&(v1, v2))
                        && !buy.contains(&(v2, v1))
                    {
                        false
                    } else {
                        true
                    }
                });

                if buy.len() == 2 && !(left_comp.is_complex() && right_comp.is_complex()) {
                    let l1 = buy[0].0;
                    let r1 = buy[0].1;
                    let l2 = buy[1].0;
                    let r2 = buy[1].1;

                    if !left_comp.is_adjacent(l1, l2) && np_config_left.is_nice_pair(l1, l2) {
                        total_plus_sell += Credit::from_integer(1)
                    }
                    if !right_comp.is_adjacent(r1, r2) && np_config_right.is_nice_pair(r1, r2) {
                        total_plus_sell += Credit::from_integer(1)
                    }
                }

                match is_complex(&check_graph) {
                    ComplexCheckResult::Complex(bridges, black_vertices) => {
                        let blocks_graph = EdgeFiltered::from_fn(&check_graph, |(v, u, _)| {
                            !bridges.contains(&(v, u)) && !bridges.contains(&(u, v))
                        });
                        let num_blocks = connected_components(&blocks_graph) - black_vertices.len();
                        let black_deg: usize = black_vertices
                            .iter()
                            .map(|v| bridges.iter().filter(|(a, b)| a == v || b == v).count())
                            .sum();
                        let new_credits = Credit::from_integer(num_blocks as i64)
                            * credit_inv.complex_block()
                            + credit_inv.complex_black(black_deg as i64)
                            + credit_inv.complex_comp();

                        if total_plus_sell - buy_credits >= new_credits {
                            return true;
                        }
                    }
                    ComplexCheckResult::NoBridges => {
                        if total_plus_sell - buy_credits >= credit_inv.large() {
                            return true;
                        }
                    }
                    ComplexCheckResult::BlackLeaf => continue,
                    ComplexCheckResult::NotConnected | ComplexCheckResult::Empty => continue,
                }
            }
        }
    } else {
        for buy in matching.into_iter().powerset().filter(|p| p.len() == 2) {
            let l1 = buy[0].0;
            let r1 = buy[0].1;
            let l2 = buy[1].0;
            let r2 = buy[1].1;

            let mut credits = total_comp_credit - Credit::from_integer(2);

            if np_config_left.is_nice_pair(l1, l2) {
                credits += Credit::from_integer(1)
            }
            if np_config_right.is_nice_pair(r1, r2) {
                credits += Credit::from_integer(1)
            }

            if credits >= credit_inv.large() {
                return true;
            }
        }
    }

    false
}

fn prove_nice_path<C: CreditInvariant>(
    path: NicePath,
    credit_inv: C,
    path_node: &mut ProofNode,
) -> bool {
    let path_len = path.nodes.len();
    let last_comp_ref = path.nodes.last().unwrap().get_comp();
    let last_graph = last_comp_ref.graph();

    let mut targets = vec![PathMatchingHits::Outside];
    for i in 0..path_len - 1 {
        targets.push(PathMatchingHits::Path(i));
    }

    for m_endpoints in last_graph.nodes().permutations(3) {
        'match_loop: for hits in targets.iter().combinations_with_replacement(2) {
            let m_path = PathMatchingEdge(m_endpoints[0], PathMatchingHits::Path(path_len - 2));
            let m1 = PathMatchingEdge(m_endpoints[1], *hits[0]);
            let m2 = PathMatchingEdge(m_endpoints[2], *hits[1]);
            let mut matching = vec![m_path, m1, m2];
            matching.sort_by_key(|m| m.hit());

            let mut matching_proof =
                ProofNode::new_all(format!("Matching [({}), ({}), ({})]", m_path, m1, m2));

            let proof_result = prove_nice_path_matching(
                &path,
                credit_inv.clone(),
                m_path,
                m1,
                m2,
                &mut matching_proof,
            );

            path_node.add_child(matching_proof);

            if !proof_result {
                return false;
            }
        }
    }

    true
}

fn check_nice_path_with_cycle<C: CreditInvariant>(
    path: &NicePath,
    m_cycle_edge: PathMatchingEdge,
    hit_and_out_np: bool,
    credit_inv: C,
    matching_node: &mut ProofNode,
) -> bool {
    // check worst-case merge
    let mut pseudo_nodes = path
        .nodes
        .split_at(m_cycle_edge.hits_path().unwrap())
        .1
        .to_vec();
    if let Some(SuperNode::Zoomed(zoomed)) = pseudo_nodes.last_mut() {
        zoomed.out_node = Some(m_cycle_edge.source())
    }
    if let Some(SuperNode::Abstract(abs)) = pseudo_nodes.first_mut() {
        abs.nice_pair = hit_and_out_np
    }
    let cycle = PseudoCycle {
        nodes: pseudo_nodes,
    };
    if cycle.value(credit_inv.clone()) >= Credit::from_integer(2) {
        matching_node.add_child(ProofNode::new_leaf(
            format!("PseudoCycle {} merged!", cycle),
            true,
        ));
        return true;
    } else {
        matching_node.add_child(ProofNode::new_leaf(
            format!("Failed worst-case merge for PseudoCycle {} ", cycle),
            false,
        ));
        return false;
    }
}

fn is_longer_nice_path_possible(
    last_comp_ref: &Component,
    np_config: &NicePairConfig,
    last_pseudo_edge: &PathMatchingEdge,
    other_matching_edge: &PathMatchingEdge,
    matching_node: &mut ProofNode,
) -> bool {
    if other_matching_edge.hits_outside() {
        if last_comp_ref.is_c6()
            || last_comp_ref.is_large()
            || np_config.is_nice_pair(last_pseudo_edge.source(), other_matching_edge.source())
        {
            matching_node.add_child(ProofNode::new_leaf(
                format!("Longer nice path found via edge ({})!", other_matching_edge),
                true,
            ));
            return true;
        } else {
            matching_node.add_child(ProofNode::new_leaf(
                format!(
                    "No longer nice path possible via edge ({})!",
                    other_matching_edge
                ),
                false,
            ));
            return false;
        }
    }
    return false;
}

// fn prove_nice_path2<C: CreditInvariant>(path: NicePath, credit_inv: C) -> bool {
//     let first_graph = path.first.get_graph();
//     let prelast_graph = path.prelast.get_graph();
//     let last_graph = path.last.get_graph();
//     let (graph, nodes) = merge_graphs(vec![first_graph, prelast_graph, last_graph]);
//     let [first_graph, prelast_graph, last_graph] = <[Graph; 3]>::try_from(nodes).ok().unwrap();

//     for (f_out, f_in, p_out, p_in, l_out, l_in) in itertools::iproduct!(
//         first_graph.nodes(),
//         first_graph.nodes(),
//         prelast_graph.nodes(),
//         prelast_graph.nodes(),
//         last_graph.nodes(),
//         last_graph.nodes()
//     ) {
//         let cycle = vec![(f_out, l_in), (l_out, p_in), (p_out, f_in)];
//         let sellable = edges_of_type(&graph, EdgeType::Sellable);
//         let total_component_credits = sum_of_credits(
//             vec![&path.first, &path.prelast, &path.last],
//             credit_inv.clone(),
//         );

//         let mut graph_copy = graph.clone();
//         for (v1, v2) in &cycle {
//             graph_copy.add_edge(*v1, *v2, EdgeType::Buyable);
//         }

//         let result = find_feasible_merge(
//             &graph_copy,
//             vec![cycle].into_iter(),
//             sellable.into_iter().powerset(),
//             credit_inv.large(),
//             credit_inv.clone(),
//             todo!(),
//         );
//         if let MergeResult::FeasibleLarge(_) | MergeResult::FeasibleComplex(_) = result {
//             //println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
//             return false;
//         }
//     }

//     true
// }

// All(NicePathEnumeration,
//     All(MatchingHots,
//         All(NicePairConfigs,
//             Any(
//                 LongerPath,
//                 All(PossibleMergeMatchings  ,
//                     Any(
//                         LocalMerge,
//                         LongerNicePathViaMatchingChange,
//                     )
//                 ),
//             )
//         )
//     )
// )

pub struct ProofContext {
    pub credit_inv: DefaultCredits,
}

pub trait Enumerator {
    type In;
    type Out;
    //type Iter: Iterator<Item = Self::Out>;

    fn msg(&self, data_in: &Self::In) -> String;

    fn iter(&self, data_in: Self::In) -> Box<dyn Iterator<Item = Self::Out>>;

    fn item_msg(&self, item: &Self::Out) -> String {
        String::new()
    }
}

pub trait Tactic {
    type In;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode;
}

pub struct Or<I, A1, A2> {
    tactic1: A1,
    tactic2: A2,
    _phantom_data: PhantomData<I>,
}

pub fn or<I, A1, A2>(tactic1: A1, tactic2: A2) -> Or<I, A1, A2> {
    Or {
        tactic1,
        tactic2,
        _phantom_data: PhantomData,
    }
}

impl<I, A1, A2> Tactic for Or<I, A1, A2>
where
    A1: Tactic,
    A2: Tactic,
    A1::In: From<I>,
    A2::In: From<I>,
    I: Clone,
{
    type In = I;

    fn action(&self, data: Self::In, context: &ProofContext) -> ProofNode {
        let mut res1 = self.tactic1.action(data.clone().into(), context);
        let mut proof = ProofNode::new_any("Or".into());

        if res1.eval() {
            proof.add_child(res1);
        } else {
            proof.add_child(self.tactic2.action(data.into(), context))
        }

        proof
    }
}

pub struct All<E, A> {
    enumerator: E,
    tactic: A,
}

pub fn all<E, A>(enumerator: E, tactic: A) -> All<E, A> {
    All { enumerator, tactic }
}

impl<E, A> Tactic for All<E, A>
where
    E: Enumerator,
    A: Tactic,
    A::In: From<E::Out>,
{
    type In = E::In;

    fn action(&self, data_in: Self::In, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_all(self.enumerator.msg(&data_in));

        self.enumerator.iter(data_in).all(|d| {
            let item_msg = self.enumerator.item_msg(&d);
            let mut res = self.tactic.action(d.into(), context);
            res = ProofNode::new_info(item_msg, res);
            let cont = res.eval();
            proof.add_child(res);
            cont
        });

        proof
    }
}

pub struct Any<E, A> {
    enumerator: E,
    tactic: A,
}

pub fn any<E, A>(enumerator: E, tactic: A) -> Any<E, A> {
    Any { enumerator, tactic }
}

impl<E, A> Tactic for Any<E, A>
where
    E: Enumerator,
    A: Tactic,
    A::In: From<E::Out>,
{
    type In = E::In;

    fn action(&self, data_in: Self::In, context: &ProofContext) -> ProofNode {
        let mut proof = ProofNode::new_any(self.enumerator.msg(&data_in));

        self.enumerator.iter(data_in).any(|d| {
            let item_msg = self.enumerator.item_msg(&d);
            let mut res = self.tactic.action(d.into(), context);
            res = ProofNode::new_info(item_msg, res);
            let cont = res.eval();
            proof.add_child(res);
            cont
        });

        proof
    }
}
