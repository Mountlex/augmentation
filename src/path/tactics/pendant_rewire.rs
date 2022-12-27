use crate::{
    path::{proof::Instance, Pidx},
    proof_tree::ProofNode,
};

pub fn check_pendant_node(instance: &Instance) -> ProofNode {
    let all_edges = instance.all_edges();
    let mut outside = instance.out_edges();
    let mut path_comps = instance.path_nodes();
    let rem_edges = instance.rem_edges();

    let last_comp_nodes = &path_comps.next().unwrap().comp.matching_nodes();

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

    let c = outside.all(|n| !last_comp_nodes.contains(n));

    let d = rem_edges.iter().all(|e| e.source_idx != Pidx::Last);

    if a && b && c && d {
        return ProofNode::new_leaf(format!("Rewire pendant node!",), true);
    } else {
        return ProofNode::new_leaf(format!("No pendant node!",), false);
    }
}
