
use itertools::Itertools;

use crate::{
    comps::Component,
    proof_logic::{Enumerator, EnumeratorTactic},
    tree::{TreeCaseInstance, TreeContext},
    types::Edge,
    Node,
};

pub struct MatchingEnum {
    size: usize
}

impl MatchingEnum {
    pub fn new(size: usize) -> Self {
        Self { size }
    }
}

pub struct MatchingEnumerator<'a> {
    instance: &'a TreeCaseInstance,
    size: usize
}

impl<'a> Enumerator<TreeCaseInstance, TreeContext> for MatchingEnumerator<'a> {
    fn iter(&self, _context: &TreeContext) -> Box<dyn Iterator<Item = TreeCaseInstance> + '_> {
        let last_idx = self.instance.comps.len() - 1;
        let edges = self.instance.edges_between(last_idx);
        let left = &self.instance.comps[last_idx - 1];
        let right = &self.instance.comps[last_idx];
        let left_matched = edges
            .iter()
            .flat_map(|e| e.endpoint_at(last_idx - 1))
            .collect_vec();
        let right_matched = edges
            .iter()
            .flat_map(|e| e.endpoint_at(last_idx))
            .collect_vec();

        let left_free: Box<dyn Iterator<Item = &Node>> = if let Component::Large(n) = left {
            Box::new(std::iter::repeat(n).take(self.size))
        } else {
            Box::new(
                left.matching_nodes()
                    .into_iter()
                    .filter(move |n| !left_matched.contains(n)),
            )
        };

        let right_free: Vec<Node> = if let Component::Large(n) = right {
            vec![*n; self.size]
        } else {
            right
                .matching_nodes()
                .into_iter()
                .filter(move |n| !right_matched.contains(n))
                .cloned()
                .collect_vec()
        };

        let instance = self.instance.clone();
       
        let iter = left_free.combinations(self.size).flat_map(move |lefts| {
            let right_free = right_free.clone();
            let instance = instance.clone();
            right_free.into_iter().permutations(self.size).map(move |rights| {
                let mut instance_clone = instance.clone();
                for (l,r) in lefts.iter().zip(rights.into_iter()) {
                    instance_clone
                    .edges
                    .push(Edge::new(**l, last_idx - 1, r, last_idx));
                }
                instance_clone
            })
        });

        Box::new(iter)
    }
}

impl EnumeratorTactic<TreeCaseInstance, TreeCaseInstance, TreeContext> for MatchingEnum {
    type Enumer<'a> = MatchingEnumerator<'a>;

    fn msg(&self, _data_in: &TreeCaseInstance) -> String {
        String::new()
    }

    fn get_enumerator<'a>(&'a self, data: &'a TreeCaseInstance) -> Self::Enumer<'a> {
        MatchingEnumerator { instance: data, size: self.size }
    }

    fn item_msg(&self, item: &TreeCaseInstance) -> String {
        format!("Edges [{}]", item.edges.iter().join(", "))
    }
}
