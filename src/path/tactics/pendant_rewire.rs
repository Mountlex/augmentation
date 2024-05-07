use crate::{
    path::PathProofNode,
    path::{instance::Instance, Pidx},
};

pub fn check_pendant_node(instance: &Instance) -> PathProofNode {
    let all_edges = instance.all_inter_comp_edges();
    let outside = instance.out_edges();
    let mut path_comps = instance.path_nodes();
    let rem_edges = instance.rem_edges();

    let last_comp_nodes = &path_comps.next().unwrap().comp.nodes();

    let a = all_edges
        .iter()
        .filter(|e| e.between_path_nodes(Pidx::Last, Pidx::Prelast))
        .count()
        == 3;

    let b = all_edges
        .iter()
        .filter(|e| e.path_incident(Pidx::Last))
        .count()
        == 3;

    let c = outside.iter().all(|n| !last_comp_nodes.contains(n));

    let d = rem_edges.iter().all(|e| e.source_idx != Pidx::Last);

    if a && b && c && d {
        PathProofNode::new_leaf("Rewire pendant node!".to_string(), true)
    } else {
        PathProofNode::new_leaf("No pendant node!".to_string(), false)
    }
}
