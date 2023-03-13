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

        let left_free: Vec<Node> = if let Component::Large(n) = left {
            vec![*n; self.size]
        } else {
            left.matching_nodes()
                .iter()
                .filter(move |n| !left_matched.contains(n))
                .cloned()
                .collect()
        };

        let right_free: Vec<Node> = if let Component::Large(n) = right {
            vec![*n; self.size]
        } else {
            right
                .matching_nodes()
                .iter()
                .filter(move |n| !right_matched.contains(n))
                .cloned()
                .collect_vec()
        };

        let iter_data = IterData {
            left: left.clone(),
            left_free,
            left_fix,
            right: right.clone(),
            right_free,
            right_fix,
            instance: self.instance.clone(),
        };

        let iter = match (left, right, left_fix == 1, right_fix == 1) {
            (Component::Large(_), Component::Large(_), _, _) => {
                self.construct_iter(IterType::Fixed, IterType::Fixed, iter_data)
            }
            (Component::Large(_), _, _, _) if right.is_cycle() => {
                self.construct_iter(IterType::Fixed, IterType::SymComb, iter_data)
            }
            (Component::Large(_), _, _, _) if !right.is_cycle() => {
                self.construct_iter(IterType::Fixed, IterType::Comb, iter_data)
            }
            (_, Component::Large(_), _, _) => {
                self.construct_iter(IterType::Comb, IterType::Fixed, iter_data)
            }
            (_, _, true, false) => self.construct_iter(IterType::Comb, IterType::Perm, iter_data),
            (_, _, _, _) if right.is_cycle() => {
                self.construct_iter(IterType::Perm, IterType::SymComb, iter_data)
            }
            (_, _, _, _) if !right.is_cycle() => {
                self.construct_iter(IterType::Perm, IterType::Comb, iter_data)
            }
            _ => panic!(), // the above two cases catch all remaining cases!
        };

        Box::new(iter)
    }
}

enum IterType {
    Fixed,
    Perm,
    Comb,
    SymComb,
}

#[derive(Clone)]
struct IterData {
    left: Component,
    left_free: Vec<Node>,
    left_fix: usize,
    right: Component,
    right_free: Vec<Node>,
    right_fix: usize,
    instance: TreeCaseInstance,
}

impl MatchingEnumerator<'_> {
    fn construct_iter(
        &self,
        left_type: IterType,
        right_type: IterType,
        data: IterData,
    ) -> Box<dyn Iterator<Item = TreeCaseInstance>> {
        match (left_type, right_type) {
            (IterType::Fixed, IterType::Fixed) => {
                assert!(data.left_free.len() == self.size);
                assert!(data.right_free.len() == self.size);
                Box::new(std::iter::once(construct_instance(
                    data.left_free.clone(),
                    data.right_free.clone(),
                    data,
                )))
            }
            (IterType::Fixed, IterType::Comb) => {
                assert!(data.left_free.len() == self.size);
                let right_free = data.right_free.clone();
                let size = self.size;
                Box::new(
                    right_free
                        .into_iter()
                        .combinations(size - data.right_fix)
                        .map(move |rights| {
                            construct_instance(data.left_free.to_vec(), rights, data.clone())
                        }),
                )
            }
            (IterType::Fixed, IterType::SymComb) => {
                assert!(data.left_free.len() == self.size);
                Box::new(data.right.symmetric_combs().into_iter().map(move |rights| {
                    construct_instance(data.left_free.to_vec(), rights.to_vec(), data.clone())
                }))
            }
            (IterType::Comb, IterType::Fixed) => {
                assert!(data.right_free.len() == self.size);
                let left_free = data.left_free.clone();
                let size = self.size;
                Box::new(
                    left_free
                        .into_iter()
                        .combinations(size - data.left_fix)
                        .map(move |lefts| {
                            construct_instance(lefts, data.right_free.to_vec(), data.clone())
                        }),
                )
            }
            (IterType::Comb, IterType::Perm) => {
                let left_free = data.left_free.clone();
                let right_free = data.right_free.clone();
                let left_fix = data.left_fix;
                let right_fix = data.right_fix;
                let size = self.size;
                Box::new(
                    left_free
                        .into_iter()
                        .combinations(size - left_fix)
                        .flat_map(move |lefts| {
                            let data_clone = data.clone();
                            right_free
                                .clone()
                                .into_iter()
                                .permutations(size - right_fix)
                                .map(move |rights| {
                                    construct_instance(lefts.clone(), rights, data_clone.clone())
                                })
                        }),
                )
            }
            (IterType::Perm, IterType::Comb) => {
                let left_free = data.left_free.clone();
                let right_free = data.right_free.clone();
                let left_fix = data.left_fix;
                let right_fix = data.right_fix;
                let size = self.size;
                Box::new(
                    left_free
                        .into_iter()
                        .permutations(size - left_fix)
                        .flat_map(move |lefts| {
                            let data_clone = data.clone();
                            right_free
                                .clone()
                                .into_iter()
                                .combinations(size - right_fix)
                                .map(move |rights| {
                                    construct_instance(lefts.clone(), rights, data_clone.clone())
                                })
                        }),
                )
            }
            (IterType::Perm, IterType::SymComb) => {
                let left_free = data.left_free.clone();
                let left_fix = data.left_fix;
                let size = self.size;
                Box::new(
                    left_free
                        .into_iter()
                        .permutations(size - left_fix)
                        .flat_map(move |lefts| {
                            let data_clone = data.clone();
                            data.right.symmetric_combs().into_iter().map(move |rights| {
                                construct_instance(
                                    lefts.clone(),
                                    rights.to_vec(),
                                    data_clone.clone(),
                                )
                            })
                        }),
                )
            }
            _ => {
                panic!()
            }
        }
    }
}

fn construct_instance(
    lefts: Vec<Node>,
    rights: Vec<Node>,
    iter_data: IterData,
) -> TreeCaseInstance {
    let last_idx = iter_data.instance.comps.len() - 1;
    let mut instance_clone = iter_data.instance;
    for (l, r) in lefts
        .into_iter()
        .chain(
            std::iter::once(iter_data.left.fixed_node())
                .take(iter_data.left_fix)
                .map(|n| n.unwrap()),
        )
        .zip(
            rights.iter().cloned().chain(
                std::iter::once(iter_data.right.fixed_node())
                    .take(iter_data.right_fix)
                    .map(|n| n.unwrap()),
            ),
        )
    {
        instance_clone
            .edges
            .push(Edge::new(l, Pidx::N(last_idx - 1), r, Pidx::N(last_idx)));
    }
    instance_clone
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
