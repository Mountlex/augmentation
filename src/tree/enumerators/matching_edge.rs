use itertools::Itertools;

use crate::{
    comps::Component,
    path::Pidx,
    proof_logic::{Enumerator, EnumeratorTactic},
    tree::{TreeCaseInstance, TreeContext},
    types::Edge,
    Node,
};

pub struct MatchingEnum {
    size: usize,
}

impl MatchingEnum {
    pub fn new(size: usize) -> Self {
        Self { size }
    }
}

pub struct MatchingEnumerator<'a> {
    instance: &'a TreeCaseInstance,
    size: usize,
}

impl<'a> Enumerator<TreeCaseInstance, TreeContext> for MatchingEnumerator<'a> {
    fn iter(&self, _context: &TreeContext) -> Box<dyn Iterator<Item = TreeCaseInstance> + '_> {
        let last_idx = self.instance.comps.len() - 1;
        let edges = self.instance.edges_between(last_idx);
        let left = &self.instance.comps[last_idx - 1];
        let right = &self.instance.comps[last_idx];
        let mut left_matched = edges
            .iter()
            .flat_map(|e| e.endpoint_at(Pidx::N(last_idx - 1)))
            .collect_vec();
        let mut right_matched = edges
            .iter()
            .flat_map(|e| e.endpoint_at(Pidx::N(last_idx)))
            .collect_vec();

        let mut left_fix = 0;
        let mut right_fix = 0;
        if last_idx == 1 {
            // left is leaf
            if let Some(fixed) = left.fixed_node() {
                if !left_matched.contains(&fixed) {
                    left_matched.push(fixed);
                    left_fix += 1;
                }
            }
        }
        if let Some(fixed) = right.fixed_node() {
            if !right_matched.contains(&fixed) {
                right_matched.push(fixed);
                right_fix += 1;
            }
        }

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

        let iter = left_free
            .permutations(self.size - left_fix)
            .flat_map(move |lefts| {
                let right_free = right_free.clone();
                let instance = instance.clone();
                right_free
                    .into_iter()
                    .permutations(self.size - right_fix)
                    .map(move |rights| {
                        let mut instance_clone = instance.clone();
                        for (l, r) in lefts
                            .iter()
                            .copied()
                            .copied()
                            .chain(std::iter::once(left.fixed_node()).take(left_fix).map(|n| n.unwrap()))
                            .zip(
                                rights
                                    .into_iter()
                                    .chain(std::iter::once(right.fixed_node()).take(right_fix).map(|n| n.unwrap())),
                            )
                        {
                            instance_clone.edges.push(Edge::new(
                                l,
                                Pidx::N(last_idx - 1),
                                r,
                                Pidx::N(last_idx),
                            ));
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
        MatchingEnumerator {
            instance: data,
            size: self.size,
        }
    }

    fn item_msg(&self, item: &TreeCaseInstance) -> String {
        format!("Edges [{}]", item.edges.iter().join(", "))
    }
}
