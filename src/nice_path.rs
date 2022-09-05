use itertools::{Itertools, iproduct};
use num_rational::Rational64;

use crate::{
    comps::{merge_graphs, Component, CreditInvariant, EdgeType, Graph, Node, merge_components_to_base},
    edges_of_type,
    local_merge::{find_feasible_merge, FeasibleMerge, MergeResult, prove_via_direct_merge}, proof_tree::ProofNode,
};

#[derive(Clone)]
struct AbstractNode {
    comp: Component,
    nice_pair: bool,
    used: bool,
}

impl AbstractNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }
}

struct ZoomedNode {
    comp: Component,
    in_node: Option<Node>,
    out_node: Option<Node>,
}

impl ZoomedNode {
    fn get_comp(&self) -> &Component {
        &self.comp
    }
}

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

    fn credit<C: CreditInvariant>(&self, credit_inv: C) -> Rational64 {
        match self {
            Node::NicePair(c) => credit_inv.credits(c) + Rational64::from_integer(1),
            Node::Any(c) => credit_inv.credits(c),
        }
    }
}

struct NicePath {
    nodes: Vec<SuperNode>,
    graph: Graph
}

fn sum_of_credits<C: CreditInvariant>(nodes: Vec<&Node>, credit_inv: C) -> Rational64 {
    nodes
        .into_iter()
        .map(|n| n.credit(credit_inv.clone()))
        .sum()
}

pub fn prove_nice_path_progress<C: CreditInvariant>(comps: Vec<Component>, credit_inv: C) {
    for (c1,c2,c3,c4,c5) in iproduct!(comps,comps,comps,comps,comps) {
        let path = vec![c1,c2,c3,c4,c5];
        let (path_graph, path) = merge_components_to_base(Graph::new(), path);

        let nodes = path.into_iter().map(|c| {
            let nice_pair = match c {
                Component::Cycle(cycle) if cycle.edge_count() <= 5 => true,
                Component::Complex(_, _, _) => true,
                _ => false,
            };
            SuperNode::Abstract(AbstractNode {
                comp: c,
                nice_pair,
                used: false
            })
        }).collect();

        let nice_path = NicePath {
            nodes,
            graph: path_graph,
        };

        if prove_nice_path(nice_path, credit_inv.clone()) {
            
        }
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

fn get_local_merge_graph(comp1: &Component, comp2: &Component, matching: &Vec<(Node, Node)>) -> Graph {
    let mut graph = comp1.graph().clone();
    for (v1,v2,t) in comp2.graph().all_edges() {
        graph.add_edge(v1,v2,*t);
    }
    for (m1, m2) in matching {
        graph.add_edge(*m1, *m2, EdgeType::Buyable);
    }
    graph
}

fn prove_nice_path<C: CreditInvariant>(path: NicePath, credit_inv: C) -> bool {
    let path_len = path.nodes.len();
    let last_comp_ref = path.nodes.last().unwrap().get_comp();
    let last_graph = last_comp_ref.graph();
    
    let targets = vec![MatchingHit::Path(0), MatchingHit::Path(1), MatchingHit::Path(2),  MatchingHit::Outside];
    for matching_nodes in last_graph.nodes().powerset().filter(|s| s.len() == 3) {
        for hits in targets.iter().permutations(2) {
            let m0 = MatchingHit::Path(path_len - 2);
            let m1 = *hits[0];
            let m2 = *hits[1];

            // Find longer nice path
            if matches!(m1, MatchingHit::Outside) {
                if last_comp_ref.is_c6() || last_comp_ref.is_large() ||  last_comp_ref.is_nice_pair(matching_nodes[0], matching_nodes[1]) {
                    return true
                }
            }
            if matches!(m2, MatchingHit::Outside) {
                if last_comp_ref.is_c6() || last_comp_ref.is_large() || last_comp_ref.is_nice_pair(matching_nodes[0], matching_nodes[2]) {
                    return true
                }
            }

            // TODO contractability of c5



            // Now if we land here, one of the matching edges should hit the path

            let mut ends = vec![m0,m1,m2];
            ends.sort();
            
            // If at least two matching edges hit same component
            if let Some(multi_hit) = ends.iter().dedup_with_count().filter(|(count, _)| *count > 1).map(|(_, hit)| hit).find(|_| true) {
                let right_matched: Vec<Node> = 
                    (matching_nodes.iter().zip(vec![m0,m1,m2])).filter(|(_,m)| m == multi_hit).map(|(v,_)| *v).collect();
                
                let left_comp = path.nodes[multi_hit.path_index().unwrap()].get_comp();

                // check for all concrete matchings if local merge is possible between both components
                for left_matched in left_comp.matching_permutations(right_matched.len()) {
                    let matching = left_matched
                    .into_iter()
                    .zip(right_matched.into_iter())
                    .map(|(l, r)| (l, r))
                    .collect_vec();
                    let graph_with_matching = get_local_merge_graph(left_comp, last_comp_ref, &matching);

                    if prove_via_direct_merge(
                        &graph_with_matching,
                        vec![left_comp, last_comp_ref],
                        credit_inv.clone(),
                        &mut ProofNode::new_any(String::new()),
                    ) {
                        return true;
                    }
                }

            }

            
            // Now if we land here, all matching edges hit different components.

        }
    }

    false
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
