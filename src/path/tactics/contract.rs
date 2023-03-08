use itertools::Itertools;

use crate::{
    path::PathProofNode,
    path::{proof::Instance, utils::hamiltonian_paths, Pidx},
};

pub fn check_contractability(instance: &Instance) -> PathProofNode {
    return check_for_comp(instance, Pidx::Last);
}

fn check_for_comp(instance: &Instance, idx: Pidx) -> PathProofNode {
    let all_edges = &instance.edges;
    let outside = &instance.outside_edges;
    let path_comps = instance.path_nodes().collect_vec();
    let rem_edges = &instance.rem_edges;
    let npc = &instance.npc;

    let comp = &path_comps[idx.raw()].comp;

    if comp.is_complex() || comp.is_large() || comp.is_c3() || comp.is_c4() {
        return PathProofNode::new_leaf(
            "Contractability check not applied: component is C3, Large or Complex".into(),
            false,
        )
        .into();
    }

    let nodes = comp.matching_nodes();
    let used_nodes = nodes
        .iter()
        .filter(|n| {
            outside.contains(n)
                || rem_edges.iter().any(|e| e.source == **n)
                || all_edges.iter().any(|e| e.node_incident(n))
        })
        .cloned()
        .collect_vec();
    let free_nodes = nodes
        .into_iter()
        .filter(|n| !used_nodes.contains(n))
        .cloned()
        .collect_vec();

    let num_edges_between_free_nodes = comp
        .graph()
        .all_edges()
        .filter(|(u, v, _)| free_nodes.contains(u) && free_nodes.contains(v))
        .count();

    let opt_lb = free_nodes.len() * 2 - num_edges_between_free_nodes;

    if opt_lb * 5 >= comp.graph().node_count() * 4 {
        let chord_implies_absent_np = free_nodes.iter().combinations(2).any(|free_edge| {
            used_nodes
                .iter()
                .combinations(2)
                .filter(|m| !npc.is_nice_pair(*m[0], *m[1]))
                .any(|m| {
                    hamiltonian_paths(*m[0], *m[1], comp.nodes())
                        .iter()
                        .any(|path| {
                            path.windows(2).all(|e| {
                                comp.is_adjacent(&e[0], &e[1])
                                    || (*free_edge[0] == e[0] && *free_edge[1] == e[1])
                                    || (*free_edge[1] == e[0] && *free_edge[0] == e[1])
                            })
                        })
                })
        });

        if chord_implies_absent_np {
            return PathProofNode::new_leaf(
                format!(
                    "Component {} is contractable and chords imply absent nice pairs!",
                    comp
                ),
                true,
            )
            .into();
        } else {
            return PathProofNode::new_leaf(
                    format!("Component {} is contractable, but there might be inner chords which don't contradict nice pairs!", comp),
                    false,
                ).into();
        }
    } else {
        return PathProofNode::new_leaf(format!("Component {} is not contractable!", comp), false)
            .into();
    }
}
