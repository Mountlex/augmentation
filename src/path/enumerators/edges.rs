use itertools::Itertools;

use crate::{
    path::{proof::Instance, InstPart, MatchingEdge, Pidx},
    types::Edge,
    Node,
};

pub fn edge_enumerator(instance: &Instance) -> Option<Box<dyn Iterator<Item = InstPart>>> {
    let path_comps = instance.path_nodes().collect_vec();
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

    let len = path_comps.len();
    //let mut path_comps = path_comps.into_iter().take(len - 1).collect_vec();
    //path_comps.sort_by_key(|p| p.comp.matching_nodes().len());
    for path_comp in path_comps.iter().take(len - 1) {
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
    for s in 2..len - 1 {
        let comp_nodes = path_comps
            .iter()
            .take(s)
            .flat_map(|c| c.comp.matching_nodes().to_vec())
            .collect_vec();
        let other_nodes = path_comps
            .iter()
            .filter(|p| p.path_idx.raw() > s)
            .flat_map(|p| p.comp.matching_nodes().to_vec())
            .collect_vec();
        if let Some(iter) = matching_iterator_between(comp_nodes, other_nodes, instance) {
            return Some(to_inst_parts(iter, nodes_to_pidx, true));
        }
    }

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
    let outside_edges_at_nodes = instance
        .out_edges()
        .filter(|n| nodes.contains(n))
        .cloned()
        .collect_vec();
    let rem_edges_at_nodes = instance
        .rem_edges()
        .into_iter()
        .map(|e| e.source)
        .filter(|n| nodes.contains(n))
        .collect_vec();
    let edges_at_nodes = instance
        .all_edges()
        .into_iter()
        .filter(|e| e.one_sided_nodes_incident(&nodes))
        .collect_vec();

    let edges_nodes = edges_at_nodes.iter().flat_map(|e| e.to_vec()).collect_vec();
    let edge_nodes_at_nodes = edges_nodes
        .into_iter()
        .filter(|n| nodes.contains(n))
        .collect_vec();

    let used_non_comp_nodes = nodes
        .iter()
        .filter(|n| {
            !n.is_comp()
                && (edge_nodes_at_nodes.contains(n)
                    || outside_edges_at_nodes.contains(n)
                    || rem_edges_at_nodes.contains(n))
        })
        .unique()
        .collect_vec();
    let num_edges_at_comp_nodes = outside_edges_at_nodes
        .iter()
        .filter(|n| n.is_comp())
        .count()
        + rem_edges_at_nodes.iter().filter(|n| n.is_comp()).count()
        + edge_nodes_at_nodes.iter().filter(|n| n.is_comp()).count();

    let free_nodes = nodes
        .clone()
        .into_iter()
        .filter(|n| {
            n.is_comp()
                || (!edge_nodes_at_nodes.contains(n)
                    && !outside_edges_at_nodes.contains(&n)
                    && !rem_edges_at_nodes.contains(n))
        })
        .collect_vec();

    if used_non_comp_nodes.len() + num_edges_at_comp_nodes < 3 {
        let free_complement = complement
            .into_iter()
            .filter(|n| {
                n.is_comp() || edges_at_nodes.iter().filter(|e| e.node_incident(n)).count() != 1
            })
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
