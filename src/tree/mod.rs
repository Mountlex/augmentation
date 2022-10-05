//mod local_merge;

use std::fmt::Display;

use itertools::Itertools;

use crate::{comps::Component, path::Pidx, types::Edge, CreditInv, Node};

mod enumerators;
mod proof;
mod tactics;
mod utils;

pub use proof::prove_tree_case;

#[derive(Debug, Clone)]
pub struct TreeCaseInstance {
    comps: Vec<Component>,
    edges: Vec<Edge>,
}

impl TreeCaseInstance {
    pub fn edges_between(&self, idx: usize) -> Vec<Edge> {
        self.edges
            .iter()
            .filter(|e| e.between_path_nodes(Pidx::N(idx - 1), Pidx::N(idx)))
            .cloned()
            .collect_vec()
    }
}

#[derive(Debug, Clone)]
pub struct ContractableCompInstance {
    instance: TreeCaseInstance,
    contr_idx: usize,
    free_nodes: Vec<Node>,
}

impl Display for TreeCaseInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Instance {} with edges [{}]",
            self.comps.iter().join(" -- "),
            self.edges.iter().join(", ")
        )
    }
}

#[derive(Clone)]
pub struct TreeContext {
    pub credit_inv: CreditInv,
    pub inner_comps: Vec<Component>,
}
