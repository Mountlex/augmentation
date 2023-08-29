use itertools::{iproduct, Itertools};
use num_traits::Zero;

use crate::{
    comps::CompType,
    path::{
        instance::Instance,
        pseudo_cycle::{CycleComp, PseudoCycle},
        NicePairConfig, PathComp,
    },
    path::{PathProofNode, Pidx},
    types::Edge,
    Credit, Node,
};

pub fn check_cycle_merge(instance: &Instance) -> PathProofNode {
    let pc = instance.pseudo_cycle().unwrap();
    let all_edges = instance.all_edges();
    let path_comps = instance.path_nodes().collect_vec();
    let npc = instance.npc();

    let cycle_value = pc.value(&path_comps, &all_edges, &npc, instance);

    if cycle_value >= Credit::from_integer(2) {
        PathProofNode::new_leaf(
            format!("Merged pseudo cycle with value {}!", cycle_value),
            true,
        )
    } else {
        PathProofNode::new_leaf(
            format!(
                "Failed cycle merge with value {}",
                //data.pseudo_cycle,
                cycle_value
            ),
            false,
        )
    }
}

struct CompValue {
    base: Credit,
    /// list of other components and the credit gained through a shortcut with this other component
    shortcuts: Vec<(Pidx, Credit)>,
}

impl CompValue {
    fn base(base_value: Credit) -> Self {
        CompValue {
            base: base_value,
            shortcuts: vec![],
        }
    }
}

impl PseudoCycle {
    pub fn value(
        &self,
        path_comps: &Vec<&PathComp>,
        all_edges: &[Edge],
        npc: &NicePairConfig,
        instance: &Instance,
    ) -> Credit {
        self.total_component_value(path_comps, all_edges, npc, instance) - self.total_edge_cost
    }

    fn total_component_value(
        &self,
        path_comps: &Vec<&PathComp>,
        all_edges: &[Edge],
        npc: &NicePairConfig,
        instance: &Instance,
    ) -> Credit {
        // let first_complex = self
        //     .cycle
        //     .iter()
        //     .enumerate()
        //     .rev()
        //     .find(|(_, n)| match n.1 {
        //         CycleComp::PathComp(idx) => path_comps[idx.raw()].comp.is_complex(),
        //         CycleComp::Rem => false,
        //     })
        //     .map(|(i, _)| i);


        let values = self
            .cycle
            .iter()
            .map(|(in_node, comp, out_node)| {
                match comp {
                    CycleComp::PathComp(idx) => {
                        let comp = path_comps[idx.raw()];
                        self.comp_value(comp, in_node, out_node, npc, all_edges, instance)
                    }
                    CycleComp::Rem => {
                        CompValue::base(instance.context.inv.two_ec_credit(4)) // non shortcutable C4
                    }
                }
            })
            .collect_vec();

        let base: Credit = values.iter().map(|v| v.base).sum();
        let best_shortcut = values
            .iter()
            .flat_map(|v| v.shortcuts.iter().map(|(_, v)| *v))
            .max()
            .unwrap_or(Credit::zero())
            .max(Credit::zero());

        base + best_shortcut
    }

    fn comp_value(
        &self,
        comp: &PathComp,
        in_node: &Node,
        out_node: &Node,
        npc: &NicePairConfig,
        all_edges: &[Edge],
        instance: &Instance,
    ) -> CompValue {
        let nice_pair = npc.is_nice_pair(*in_node, *out_node);

        let path_comps = instance.path_nodes().collect_vec();
        let credit_inv = &instance.context.inv;

        let cycle_indices = self
            .cycle
            .iter()
            .flat_map(|(_, c, _)| match c {
                CycleComp::PathComp(idx) => Some(idx),
                CycleComp::Rem => None,
            })
            .cloned()
            .collect_vec();

        let incident_edges = all_edges
            .iter()
            .filter(|e| e.path_incident(comp.path_idx))
            .collect_vec();

        match comp.comp.comp_type() {
            CompType::Cycle(4) => {
                if nice_pair {
                    if comp.comp.is_adjacent(in_node, out_node) {
                        let local_merge_credits = iproduct!(incident_edges.clone(), incident_edges)
                            .filter(|(e1, e2)| {
                                // pair of edges that hits the same comp but not this cycle
                                e1.other_idx(comp.path_idx) == e2.other_idx(comp.path_idx)
                                    && !cycle_indices
                                        .contains(&e2.other_idx(comp.path_idx).unwrap())
                            })
                            .map(|(e1, e2)| {
                                let n1 = e1.endpoint_at(comp.path_idx).unwrap();
                                let n2 = e2.endpoint_at(comp.path_idx).unwrap();

                                let hit_comp = path_comps
                                    .iter()
                                    .find(|c| c.path_idx == e2.other_idx(comp.path_idx).unwrap())
                                    .unwrap();

                                // Credit for shortcutting the other side
                                let other_shortcut = if npc.is_nice_pair(
                                    e1.endpoint_at(hit_comp.path_idx).unwrap(),
                                    e2.endpoint_at(hit_comp.path_idx).unwrap(),
                                ) {
                                    Credit::from_integer(1)
                                } else {
                                    Credit::from_integer(0)
                                };

                                let credit = if !(n1 == *in_node && n2 == *out_node)
                                    && !(n2 == *in_node && n1 == *out_node)
                                    && comp.comp.is_adjacent(&n1, &n2)
                                {
                                    // in this case we can double shortcut C4
                                    credit_inv.credits(&hit_comp.comp) - Credit::from_integer(2)
                                        + other_shortcut
                                        + Credit::from_integer(1)
                                } else {
                                    // in this case we cannot double shortcut C4
                                    credit_inv.credits(&hit_comp.comp) - Credit::from_integer(2)
                                        + other_shortcut
                                };

                                (credit, hit_comp.path_idx)
                            })
                            .collect_vec();

                        let mut value = CompValue::base(
                            // +1 for shortcutting this component
                            credit_inv.credits(&comp.comp) + Credit::from_integer(1),
                        );

                        for (c, idx) in local_merge_credits {
                            if c > Credit::from_integer(0) {
                                value.shortcuts.push((idx, c));
                            }
                        }

                        value
                    } else {
                        CompValue::base(
                            // +1 for shortcutting this component
                            credit_inv.credits(&comp.comp) + Credit::from_integer(1),
                        )
                    }
                } else {
                    // Cannot shortcut C4 with cycle in and out
                    // if in_node != out_node {
                    //     // cannot be adjacent in this case!
                    //     let local_merge_credits = iproduct!(incident_edges.clone(), incident_edges)
                    //         .filter(|(e1, e2)| {
                    //             // pair of edges that hits the same comp but not this cycle
                    //             e1.other_idx(comp.path_idx) == e2.other_idx(comp.path_idx)
                    //                 && !cycle_indices
                    //                     .contains(&e2.other_idx(comp.path_idx).unwrap())
                    //         })
                    //         .map(|(e1, e2)| {
                    //             let hit_comp = path_comps
                    //                 .iter()
                    //                 .find(|c| c.path_idx == e2.other_idx(comp.path_idx).unwrap())
                    //                 .unwrap();
                    //             let credit = if npc.is_nice_pair(
                    //                 e1.endpoint_at(hit_comp.path_idx).unwrap(),
                    //                 e2.endpoint_at(hit_comp.path_idx).unwrap(),
                    //             ) {
                    //                 credit_inv.credits(&hit_comp.comp) // we make two shortcuts, so pay nothing for new edges
                    //             } else {
                    //                 credit_inv.credits(&hit_comp.comp) - Credit::from_integer(1)
                    //                 // we make only one shortcut and only pay one new edge
                    //             };
                    //             (credit, hit_comp.path_idx)
                    //         })
                    //         .collect_vec();

                    //     let mut value =
                    //         CompValue::base(credit_inv.credits(&comp.comp)); // no base shortcut

                    //     for (c, idx) in local_merge_credits {
                    //         if c > Credit::from_integer(0) {
                    //             value.shortcuts.push((idx, c));
                    //         }
                    //     }

                    //     value
                    // } else {
                    // in_node == out_node

                    // either in == out or !adj(in, out)
                    let local_merge_credits = iproduct!(incident_edges.clone(), incident_edges)
                        .filter(|(e1, e2)| {
                            // pair of edges that hits the same comp but not this cycle
                            e1.other_idx(comp.path_idx) == e2.other_idx(comp.path_idx)
                                && !cycle_indices.contains(&e2.other_idx(comp.path_idx).unwrap())
                        })
                        .map(|(e1, e2)| {
                            let n1 = e1.endpoint_at(comp.path_idx).unwrap();
                            let n2 = e2.endpoint_at(comp.path_idx).unwrap();

                            let hit_comp = path_comps
                                .iter()
                                .find(|c| c.path_idx == e2.other_idx(comp.path_idx).unwrap())
                                .unwrap();

                            let other_shortcut = if npc.is_nice_pair(
                                e1.endpoint_at(hit_comp.path_idx).unwrap(),
                                e2.endpoint_at(hit_comp.path_idx).unwrap(),
                            ) {
                                Credit::from_integer(1)
                            } else {
                                Credit::from_integer(0)
                            };

                            let credit = if !npc.is_nice_pair(n1, n2) {
                                // in this case we cannot shortcut C4
                                credit_inv.credits(&hit_comp.comp) - Credit::from_integer(2)
                                    + other_shortcut
                            } else {
                                // in this case we can shortcut C4
                                credit_inv.credits(&hit_comp.comp) - Credit::from_integer(2)
                                    + other_shortcut
                                    + Credit::from_integer(1)
                            };

                            (credit, hit_comp.path_idx)
                        })
                        .collect_vec();

                    let mut value = CompValue::base(credit_inv.credits(&comp.comp));

                    for (c, idx) in local_merge_credits {
                        if c > Credit::from_integer(0) {
                            value.shortcuts.push((idx, c));
                        }
                    }

                    value
                    //}
                }
            }
            CompType::Cycle(_) if !comp.used => {
                if nice_pair {
                    CompValue::base(
                        instance.context.inv.credits(&comp.comp) + Credit::from_integer(1),
                    )
                // shortcut!
                } else {
                    //return credit_inv.credits(&comp.comp);
                    let (upper, lower) = comp.comp.paths_between(in_node, out_node);

                    let local_merge_credits = iproduct!(incident_edges.clone(), incident_edges)
                        .filter(|(e1, e2)| {
                            // edges must hit same vertec
                            e1.other_idx(comp.path_idx) == e2.other_idx(comp.path_idx)
                                && !cycle_indices.contains(&e2.other_idx(comp.path_idx).unwrap())
                        })
                        .filter(|(e1, e2)| {
                            let n1 = e1.endpoint_at(comp.path_idx).unwrap();
                            let n2 = e2.endpoint_at(comp.path_idx).unwrap();

                            // one edge hits upper, the other hits lower
                            (upper.contains(&n1) && lower.contains(&n2))
                                || (upper.contains(&n2) && lower.contains(&n1))
                        })
                        .map(|(e1, e2)| {
                            let hit_comp = path_comps
                                .iter()
                                .find(|c| c.path_idx == e2.other_idx(comp.path_idx).unwrap())
                                .unwrap();

                            let n1 = e1.endpoint_at(comp.path_idx).unwrap();
                            let n2 = e2.endpoint_at(comp.path_idx).unwrap();

                            let other_shortcut = if npc.is_nice_pair(
                                e1.endpoint_at(hit_comp.path_idx).unwrap(),
                                e2.endpoint_at(hit_comp.path_idx).unwrap(),
                            ) {
                                Credit::from_integer(1)
                            } else {
                                Credit::from_integer(0)
                            };

                            let credit = if ((upper.contains(&n1) && lower.contains(&n2))
                                || (upper.contains(&n2) && lower.contains(&n1)))
                                && ((comp.comp.is_adjacent(&n1, in_node)
                                    && comp.comp.is_adjacent(&n2, out_node))
                                    || (comp.comp.is_adjacent(&n2, in_node)
                                        && comp.comp.is_adjacent(&n1, out_node)))
                            {
                                // double shortcut this comp
                                credit_inv.credits(&hit_comp.comp) + other_shortcut
                            } else if npc.is_nice_pair(n1, n2) {
                                // single shortcut this comp
                                credit_inv.credits(&hit_comp.comp) + other_shortcut
                                    - Credit::from_integer(1)
                            } else {
                                // no shortcut in this comp
                                credit_inv.credits(&hit_comp.comp) + other_shortcut
                                    - Credit::from_integer(2)
                            };
                            (credit, hit_comp.path_idx)
                        })
                        .collect_vec();

                    let mut value = CompValue::base(credit_inv.credits(&comp.comp));

                    for (c, idx) in local_merge_credits {
                        if c > Credit::from_integer(0) {
                            value.shortcuts.push((idx, c));
                        }
                    }

                    value
                }
            }
            CompType::Cycle(_) if comp.used => {
                assert!(comp.comp.is_c5());
                if in_node != out_node {
                    CompValue::base(credit_inv.two_ec_credit(4) + credit_inv.two_ec_credit(5))
                } else {
                    CompValue::base(credit_inv.credits(&comp.comp))
                }
            }
            CompType::Large => CompValue::base(credit_inv.credits(&comp.comp)),
            _ => panic!(),
        }
    }
}
