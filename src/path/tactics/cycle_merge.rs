use itertools::{iproduct, Itertools};

use crate::{
    comps::CompType,
    path::PathProofNode,
    path::{
        instance::Instance,
        pseudo_cycle::{CycleComp, PseudoCycle},
        utils::complex_cycle_value_base,
        NicePairConfig, PathComp,
    },
    types::Edge,
    Credit, Node,
};

pub fn check_cycle_merge(instance: &Instance) -> PathProofNode {
    let pc = instance.pseudo_cycle().unwrap();
    let all_edges = instance.all_edges();
    let path_comps = instance.path_nodes().collect_vec();
    let npc = instance.npc();

    let mut cycle_value = pc.value(&path_comps, &all_edges, &npc, instance);

    let complex = pc.cycle.iter().any(|(_, comp, _)| match comp {
        CycleComp::PathComp(idx) => path_comps[idx.raw()].comp.is_complex(),
        CycleComp::Rem => false,
    });
    if complex {
        // 2c due to gainful bridge covering. We convert the resulting complex to a large
        cycle_value += Credit::from_integer(1) * instance.context.inv.c
    }

    if complex && cycle_value >= Credit::from_integer(1) {
        PathProofNode::new_leaf(
            format!(
                "Merged pseudo cycle with to a block with value {}!",
                cycle_value
            ),
            true,
        )
    } else if cycle_value >= Credit::from_integer(2) {
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
        let first_complex = self
            .cycle
            .iter()
            .enumerate()
            .rev()
            .find(|(_, n)| match n.1 {
                CycleComp::PathComp(idx) => path_comps[idx.raw()].comp.is_complex(),
                CycleComp::Rem => false,
            })
            .map(|(i, _)| i);

        self.cycle
            .iter()
            .enumerate()
            .map(|(j, (in_node, comp, out_node))| {
                let lower_complex = first_complex.is_some() && first_complex.unwrap() > j;

                match comp {
                    CycleComp::PathComp(idx) => {
                        let comp = path_comps[idx.raw()];
                        self.comp_value(
                            comp,
                            in_node,
                            out_node,
                            npc,
                            all_edges,
                            instance,
                            lower_complex,
                        )
                    }
                    CycleComp::Rem => {
                        instance.context.inv.two_ec_credit(4) // non shortcutable triangle
                    }
                }
            })
            .sum()
    }

    fn comp_value(
        &self,
        comp: &PathComp,
        in_node: &Node,
        out_node: &Node,
        npc: &NicePairConfig,
        all_edges: &[Edge],
        instance: &Instance,
        lower_complex: bool,
    ) -> Credit {
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

                                let other_shortcut = if npc.is_nice_pair(
                                    e1.endpoint_at(hit_comp.path_idx).unwrap(),
                                    e2.endpoint_at(hit_comp.path_idx).unwrap(),
                                ) {
                                    Credit::from_integer(1)
                                } else {
                                    Credit::from_integer(0)
                                };

                                if !(n1 == *in_node && n2 == *in_node)
                                    && !(n2 == *in_node && n1 == *in_node)
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
                                }
                            })
                            .max();

                        if let Some(add) = local_merge_credits {
                            credit_inv.credits(&comp.comp) + Credit::from_integer(1) + add
                        } else {
                            credit_inv.credits(&comp.comp) + Credit::from_integer(1)
                        }
                    } else {
                        credit_inv.credits(&comp.comp) + Credit::from_integer(1)
                    }
                } else {
                    // case of no nice pair
                    if in_node != out_node {
                        // we can always shortcut C4 in this case
                        let local_merge_credits = iproduct!(incident_edges.clone(), incident_edges)
                            .filter(|(e1, e2)| {
                                // pair of edges that hits the same comp but not this cycle
                                e1.other_idx(comp.path_idx) == e2.other_idx(comp.path_idx)
                                    && !cycle_indices
                                        .contains(&e2.other_idx(comp.path_idx).unwrap())
                            })
                            .map(|(e1, e2)| {
                                let hit_comp = path_comps
                                    .iter()
                                    .find(|c| c.path_idx == e2.other_idx(comp.path_idx).unwrap())
                                    .unwrap();
                                if npc.is_nice_pair(
                                    e1.endpoint_at(hit_comp.path_idx).unwrap(),
                                    e2.endpoint_at(hit_comp.path_idx).unwrap(),
                                ) {
                                    credit_inv.credits(&hit_comp.comp) // we make two shortcuts
                                } else {
                                    credit_inv.credits(&hit_comp.comp) - Credit::from_integer(1)
                                    // we make only one shortcut
                                }
                            })
                            .max();

                        if let Some(add) = local_merge_credits {
                            credit_inv.credits(&comp.comp) + add
                        } else {
                            credit_inv.credits(&comp.comp)
                        }
                    } else {
                        // in_node == out_node
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

                                let other_shortcut = if npc.is_nice_pair(
                                    e1.endpoint_at(hit_comp.path_idx).unwrap(),
                                    e2.endpoint_at(hit_comp.path_idx).unwrap(),
                                ) {
                                    Credit::from_integer(1)
                                } else {
                                    Credit::from_integer(0)
                                };

                                if (n1 == *in_node || n2 == *in_node)
                                    && !comp.comp.is_adjacent(&n1, &n2)
                                {
                                    // in this case we cannot shortcut C4
                                    credit_inv.credits(&hit_comp.comp) - Credit::from_integer(2)
                                        + other_shortcut
                                } else {
                                    // in this case we can shortcut C4
                                    credit_inv.credits(&hit_comp.comp) - Credit::from_integer(2)
                                        + other_shortcut
                                        + Credit::from_integer(1)
                                }
                            })
                            .max();

                        if let Some(add) = local_merge_credits {
                            credit_inv.credits(&comp.comp) + add
                        } else {
                            credit_inv.credits(&comp.comp)
                        }
                    }
                }
            }
            CompType::Cycle(_) if !comp.used => {
                if nice_pair {
                    instance.context.inv.credits(&comp.comp) + Credit::from_integer(1)
                // shortcut!
                } else {
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

                                if ((upper.contains(&n1) && lower.contains(&n2))
                                || (upper.contains(&n2) && lower.contains(&n1))) && ((comp.comp.is_adjacent(&n1, in_node) && comp.comp.is_adjacent(&n2, out_node)) || (comp.comp.is_adjacent(&n2, in_node) && comp.comp.is_adjacent(&n1, out_node))) {
                                    credit_inv.credits(&hit_comp.comp) + other_shortcut
                                } else if comp.comp.is_adjacent(&n1, &n2) {
                                    credit_inv.credits(&hit_comp.comp) + other_shortcut - Credit::from_integer(1)
                                } else {
                                    credit_inv.credits(&hit_comp.comp) + other_shortcut
                                }
                        })
                        .max();

                    if let Some(add) = local_merge_credits {
                        credit_inv.credits(&comp.comp) + add
                    } else {
                        credit_inv.credits(&comp.comp)
                    }
                }
            }
            CompType::Cycle(_) if comp.used => {
                assert!(comp.comp.is_c5());
                if in_node != out_node {
                    credit_inv.two_ec_credit(4) + credit_inv.two_ec_credit(5)
                } else {
                    credit_inv.credits(&comp.comp)
                }
            }
            CompType::Large => credit_inv.credits(&comp.comp),
            CompType::Complex => {
                let complex = if lower_complex {
                    credit_inv.complex_comp()
                } else {
                    Credit::from_integer(0)
                };
                if nice_pair {
                    complex
                        + complex_cycle_value_base(
                            credit_inv,
                            &comp.comp.graph(),
                            *in_node,
                            *out_node,
                        )
                } else {
                    complex
                        + complex_cycle_value_base(
                            credit_inv,
                            &comp.comp.graph(),
                            *in_node,
                            *out_node,
                        )
                }
            }
            _ => panic!(),
        }
    }
}
