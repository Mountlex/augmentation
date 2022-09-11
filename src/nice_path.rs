use core::panic;
use std::fmt::Write;
use std::marker::PhantomData;
use std::ops::Range;
use std::path;
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
    MatchingNodesEnumerator, MatchingNodesEnumeratorOutput, NPCEnumOutput, NPCEnumerator,
    PathEnumerator, PathEnumeratorInput,
};
use crate::tactics::{
    LocalComplexMerge, LocalMerge, LongerNicePathViaMatchingSwap, LongerPathTactic, CycleMerge,
};
use crate::{
    comps::{
        merge_components_to_base, merge_graphs, Component, CreditInvariant, EdgeType, Graph, Node,
    },
    edges_of_type,
    local_merge::{find_feasible_merge, prove_via_direct_merge, FeasibleMerge, MergeResult},
    proof_tree::ProofNode,
    Credit,
};



pub fn prove_nice_path_progress<C: CreditInvariant>(
    comps: Vec<Component>,
    credit_inv: C,
    output_dir: PathBuf,
    output_depth: usize
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
            .print_tree(&mut buf, 0, output_depth)
            .expect("Unable to format tree");
        std::fs::write(filename, buf).expect("Unable to write file");
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
