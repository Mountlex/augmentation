use std::fmt::Display;

use itertools::Itertools;

use crate::{
    comps::CreditInvariant,
    path::{
        proof::{ProofContext, Statistics, Tactic},
        MatchingEdge, PathHit, PathInstance, PathMatchingInstance, SuperNode,
    },
    proof_tree::ProofNode,
    Credit,
};

pub struct CycleMerge {
    num_calls: usize,
    num_proofs: usize,
}

impl CycleMerge {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for CycleMerge {
    fn print_stats(&self) {
        println!("Cycle merge {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<PathMatchingInstance> for CycleMerge {
    fn action(&mut self, data: &PathMatchingInstance, context: &mut ProofContext) -> ProofNode {
        self.num_calls += 1;

        let cycle_edges = data
            .matching
            .other_edges
            .iter()
            .filter(|m_edge| matches!(m_edge.hit(), PathHit::Path(r) if r <= context.path_len - 3))
            .collect_vec();

        let mut proof = ProofNode::new_any("Any cycle merge".into());

        // Try worst-case merge
        // TODO also good cases and then exclude the rest
        let mut cases_remain: Vec<MergeCases> = vec![];
        for m_edge in cycle_edges {
            if check_nice_path_with_cycle(
                &data.path,
                &m_edge,
                false,
                context.credit_inv.clone(),
                &mut proof,
            ) {
                if proof.eval().success() {
                    self.num_proofs += 1;
                }
                return proof;
            } else if check_nice_path_with_cycle(
                &data.path,
                &m_edge,
                true,
                context.credit_inv.clone(),
                &mut proof,
            ) {
                cases_remain.push(MergeCases::NoNicePair(m_edge.clone()))
                // it remains to check merge for non-nice pair hit
            } else {
                cases_remain.push(MergeCases::NoNicePair(m_edge.clone()));
                cases_remain.push(MergeCases::NicePair(m_edge.clone()));
                // it remains to check merge for nice pair and non-nice pair
            }
        }

        proof
    }

    fn precondition(&self, data: &PathMatchingInstance, context: &ProofContext) -> bool {
        // If we land here, we want that at least one matching edge hits C_j for j <= l - 2.
        data.matching
            .other_edges
            .iter()
            .filter(|m_edge| matches!(m_edge.hit(), PathHit::Path(r) if r <= context.path_len - 3))
            .count()
            > 0
    }
}

pub enum MergeCases {
    NoNicePair(MatchingEdge),
    NicePair(MatchingEdge),
}

fn check_nice_path_with_cycle<C: CreditInvariant>(
    path: &PathInstance,
    cycle_edge: &MatchingEdge,
    cycle_edge_hits_np: bool,
    credit_inv: C,
    proof: &mut ProofNode,
) -> bool {
    // check worst-case merge
    let mut pseudo_nodes = path
        .nodes
        .split_at(cycle_edge.hits_path().unwrap())
        .1
        .to_vec();
    if let Some(SuperNode::Zoomed(zoomed)) = pseudo_nodes.last_mut() {
        zoomed.out_node = Some(cycle_edge.source())
    }
    if let Some(SuperNode::Abstract(abs)) = pseudo_nodes.first_mut() {
        abs.nice_pair = cycle_edge_hits_np
    }
    let cycle = PseudoCycle {
        nodes: pseudo_nodes,
    };

    let cycle_value = cycle.value(credit_inv.clone());
    if cycle_value >= Credit::from_integer(2) {
        proof.add_child(ProofNode::new_leaf_success(
            format!("PseudoCycle {} merged!", cycle),
            cycle_value == Credit::from_integer(2),
        ));
        return true;
    } else {
        proof.add_child(ProofNode::new_leaf(
            format!("Failed worst-case merge for PseudoCycle {} ", cycle),
            false,
        ));
        return false;
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
                    SuperNode::Zoomed(zoomed) => zoomed.value(credit_inv.clone(), lower_complex),
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
