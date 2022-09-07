use core::panic;
use std::fmt::Write;
use std::{collections::HashMap, fmt::Display, path::PathBuf};

use itertools::{iproduct, Itertools};
use petgraph::{
    algo::matching,
    visit::{depth_first_search, Control, DfsEvent, IntoNeighbors},
};

use crate::proof_tree::Tree;
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
struct AbstractNode {
    comp: Component,
    nice_pair: bool,
    used: bool,
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
struct ZoomedNode {
    comp: Component,
    in_node: Option<Node>,
    out_node: Option<Node>,
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

        if self.comp.is_nice_pair(cycle_in, cycle_out) {
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
enum SuperNode {
    Zoomed(ZoomedNode),
    Abstract(AbstractNode),
}

impl SuperNode {
    fn get_comp(&self) -> &Component {
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
struct NicePath {
    nodes: Vec<SuperNode>,
    graph: Graph,
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
struct PseudoCycle {
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
enum PseudoNode {
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

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum MatchingHit {
    Path(usize),
    Outside,
}

impl MatchingHit {
    fn path_index(&self) -> Option<usize> {
        match self {
            MatchingHit::Path(i) => Some(*i),
            MatchingHit::Outside => None,
        }
    }
}

impl Display for MatchingHit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MatchingHit::Path(j) => write!(f, "{}. component", j),
            MatchingHit::Outside => write!(f, "Outside path"),
        }
    }
}

fn get_local_merge_graph(
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

fn prove_nice_path<C: CreditInvariant>(
    path: NicePath,
    credit_inv: C,
    path_node: &mut ProofNode,
) -> bool {
    let path_len = path.nodes.len();
    let last_comp_ref = path.nodes.last().unwrap().get_comp();
    let last_graph = last_comp_ref.graph();

    let mut targets = vec![MatchingHit::Outside];
    for i in 0..path_len - 1 {
        targets.push(MatchingHit::Path(i));
    }

    for m_endpoints in last_graph.nodes().permutations(3) {
        'match_loop: for hits in targets.iter().combinations_with_replacement(2) {
            let m0 = MatchingHit::Path(path_len - 2); // hit second to last component
            let m1 = *hits[0];
            let m2 = *hits[1];

            let mut matching_node = ProofNode::new_any(format!(
                "Matching [({} -- {}), ({} -- {}), ({} -- {})]",
                m_endpoints[0], m0, m_endpoints[1], m1, m_endpoints[2], m2
            ));

            // Find longer nice path
            if is_longer_nice_path_possible(last_comp_ref, m_endpoints[0], m_endpoints[1], m1, &mut matching_node) {
                path_node.add_child(matching_node);
                continue 'match_loop;
            }
            if is_longer_nice_path_possible(last_comp_ref, m_endpoints[0], m_endpoints[2], m2, &mut matching_node) {
                path_node.add_child(matching_node);
                continue 'match_loop;
            }

            // TODO change last matching edge if there are two edges between second to last and last comp, then try longer nice path again!

            // TODO contractability of c5

            // Now if we land here, one of the matching edges should hit the path

            let mut hits = vec![m0, m1, m2];
            hits.sort();
            // check if we can do a local merge using matching edges
            for (num_edges, hit_comp) in hits.iter().dedup_with_count() {
                if let MatchingHit::Path(hit_comp_idx) = hit_comp {
                    let right_matched: Vec<Node> = (m_endpoints.iter().zip(vec![m0, m1, m2]))
                        .filter(|(_, m)| m == hit_comp)
                        .map(|(v, _)| *v)
                        .collect();
                    assert_eq!(right_matched.len(), num_edges);

                    let left_comp = path.nodes[*hit_comp_idx].get_comp();

                    // check for all concrete matchings if local merge is possible between both components
                    let result = left_comp
                        .matching_permutations(right_matched.len())
                        .into_iter()
                        .all(|left_matched| {
                            let matching = left_matched
                                .into_iter()
                                .zip(right_matched.iter())
                                .map(|(l, r)| (l, *r))
                                .collect_vec();
                            let graph_with_matching =
                                get_local_merge_graph(left_comp, last_comp_ref, &matching);

                            prove_via_direct_merge(
                                &graph_with_matching,
                                vec![left_comp, last_comp_ref],
                                credit_inv.clone(),
                                &mut ProofNode::new_any(String::new()),
                            )
                        });

                    if result {
                        matching_node.add_child(ProofNode::new_leaf(
                            format!(
                            "Local merge between {}. and last component using {} matching edges!",
                            hit_comp_idx,
                            num_edges
                        ),
                            true,
                        ));
                        path_node.add_child(matching_node);
                        continue 'match_loop;
                    } else {
                        matching_node.add_child(ProofNode::new_leaf(
                            format!(
                                "No local merge between {}. and last component possible!",
                                hit_comp_idx
                            ),
                            false,
                        ));
                    }
                }
            }

            // If we land here, we want that at least one matching edge hits C_j for j <= l - 2.
            if !(matches!(m1, MatchingHit::Path(j) if j <= path_len - 3)
                || matches!(m2, MatchingHit::Path(j) if j <= path_len - 3))
            {
                matching_node.add_child(ProofNode::new_leaf(
                    format!("There are no matching edges forming cycles! Aborting"),
                    false,
                ));
                path_node.add_child(matching_node);
                return false;
            }

            // Select one of the matching edges TODO
            let (cycle_edge_out, cycle_edge_comp_in): (Node, usize) =
                if let MatchingHit::Path(r) = m1 {
                    if r <= path_len - 3 {
                        (m_endpoints[1], r)
                    } else {
                        (m_endpoints[2], m2.path_index().unwrap())
                    }
                } else {
                    (m_endpoints[2], m2.path_index().unwrap())
                };

            // Replace final node of path
            let mut path = path.clone();
            *path.nodes.last_mut().unwrap() = SuperNode::Zoomed(ZoomedNode {
                comp: path.nodes.last().unwrap().get_comp().clone(),
                in_node: Some(m_endpoints[0]),
                out_node: None,
            });

            // check worst-case merge
            let mut pseudo_nodes = path.nodes.split_at(cycle_edge_comp_in).1.to_vec();
            if let Some(SuperNode::Zoomed(zoomed)) = pseudo_nodes.last_mut() {
                zoomed.out_node = Some(cycle_edge_out)
            }
            if let Some(SuperNode::Abstract(abs)) = pseudo_nodes.first_mut() {
                abs.nice_pair = false
            }
            let cycle = PseudoCycle {
                nodes: pseudo_nodes,
            };
            if cycle.value(credit_inv.clone()) >= Credit::from_integer(2) {
                matching_node.add_child(ProofNode::new_leaf(
                    format!("PseudoCycle {} merged!", cycle),
                    true,
                ));
                path_node.add_child(matching_node);
                continue 'match_loop;
            } else {
                matching_node.add_child(ProofNode::new_leaf(
                    format!("Failed worst-case merge for PseudoCycle {} ", cycle),
                    false,
                ));
            }

            matching_node.add_child(ProofNode::new_leaf(format!("Tactics exhausted!"), false));
            path_node.add_child(matching_node);
            return false
        }
    }

    true
}

fn is_longer_nice_path_possible(last_comp_ref: &Component, last_in: Node, other_in: Node, other_hit: MatchingHit, matching_node: &mut ProofNode) -> bool {
    if matches!(other_hit, MatchingHit::Outside) {
        if last_comp_ref.is_c6()
            || last_comp_ref.is_large()
            || last_comp_ref.is_nice_pair(last_in, other_in)
        {
            matching_node.add_child(ProofNode::new_leaf(
                format!(
                    "Longer nice path found via edge ({} -- {})!",
                    other_in, other_hit
                ),
                true,
            ));
            return true
        } else {
            matching_node.add_child(ProofNode::new_leaf(
                format!(
                    "No longer nice path possible via edge ({} -- {})!",
                    other_in, other_hit
                ),
                false,
            ));
            return false
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
