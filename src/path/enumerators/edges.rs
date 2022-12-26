use itertools::Itertools;

use crate::{
    path::{proof::Instance, InstPart, MatchingEdge, Pidx},
    types::Edge,
    Node,
};

pub fn edge_enumerator(instance: &Instance) -> Option<Box<dyn Iterator<Item = InstPart>>> {
    let mut path_comps = instance.path_nodes().collect_vec();
    let old_path_len = path_comps.len();

    let mut nodes_to_pidx: Vec<Option<Pidx>> = vec![None; old_path_len * 10];
    for path_comp in &path_comps {
        for node in path_comp.comp.matching_nodes() {
            nodes_to_pidx[node.get_id() as usize] = Some(path_comp.path_idx.clone());
        }
    }

    // Prio 1: Last comp gets 3-matching
    let last_nodes = path_comps.first().unwrap().comp.matching_nodes().to_vec();
    let other_nodes = path_comps
        .iter()
        .skip(1)
        .flat_map(|p| p.comp.matching_nodes().to_vec())
        .collect_vec();
    if let Some(iter) = matching_iterator_between(last_nodes, other_nodes, instance) {
        return Some(to_inst_parts(iter, nodes_to_pidx, true));
    }

    // Prio 2: Single 3-matchings
    path_comps.sort_by_key(|p| p.comp.matching_nodes().len());
    for path_comp in &path_comps {
        let comp_nodes = path_comp.comp.matching_nodes().to_vec();
        let other_nodes = path_comps
            .iter()
            .filter(|p| p.path_idx != path_comp.path_idx)
            .flat_map(|p| p.comp.matching_nodes().to_vec())
            .collect_vec();
        if let Some(iter) = matching_iterator_between(comp_nodes, other_nodes, instance) {
            return Some(to_inst_parts(iter, nodes_to_pidx, true));
        }
    }

    // Prio 3: Larger comps

    // Prio 4: Edges due to contractablility

    None
}

fn to_inst_parts(
    iter: Box<dyn Iterator<Item = (Node, Hit)>>,
    nodes_to_pidx: Vec<Option<Pidx>>,
    matching: bool,
) -> Box<dyn Iterator<Item = InstPart>> {
    Box::new(iter.map(move |(node, hit)| {
        let mut part = InstPart::empty();
        match hit {
            Hit::Outside => part.out_edges.push(node),
            Hit::RemPath => part.rem_edges.push(MatchingEdge {
                source: node,
                source_idx: nodes_to_pidx[node.get_id() as usize].unwrap().clone(),
                matching,
            }),
            Hit::Node(hit_node) => part.edges.push(Edge::new(
                node,
                nodes_to_pidx[node.get_id() as usize].unwrap().clone(),
                hit_node,
                nodes_to_pidx[hit_node.get_id() as usize].unwrap().clone(),
            )),
        }
        part
    }))
}

#[derive(Clone)]
enum Hit {
    Outside,
    RemPath,
    Node(Node),
}

fn matching_iterator_between(
    nodes: Vec<Node>,
    complement: Vec<Node>,
    instance: &Instance,
) -> Option<Box<dyn Iterator<Item = (Node, Hit)>>> {
    let outside_edges = instance.out_edges().cloned().collect_vec();
    let rem_edges = instance
        .rem_edges()
        .into_iter()
        .map(|e| e.source)
        .collect_vec();

    let no_outside_or_rem_edges = nodes
        .iter()
        .filter(|n| !outside_edges.contains(n) && !rem_edges.contains(n))
        .cloned()
        .collect_vec();

    let edges = instance
        .all_edges()
        .into_iter()
        .filter(|e| e.nodes_incident(&no_outside_or_rem_edges))
        .collect_vec();
    let edge_nodes = edges.iter().flat_map(|e| e.to_vec()).collect_vec();

    let free_nodes = no_outside_or_rem_edges
        .into_iter()
        .filter(|n| !edge_nodes.contains(n))
        .collect_vec();

    if nodes.len() - free_nodes.len() < 3 {
        let free_complement = complement
            .into_iter()
            .filter(|n| edges.iter().filter(|e| e.node_incident(n)).count() != 1)
            .collect_vec();

        let mut hits = free_complement
            .into_iter()
            .map(|n| Hit::Node(n))
            .collect_vec();
        hits.push(Hit::Outside);
        hits.push(Hit::RemPath);

        let iter = free_nodes
            .into_iter()
            .flat_map(move |n1| hits.clone().into_iter().map(move |hit| (n1, hit)));

        return Some(Box::new(iter));
    }

    None
}
