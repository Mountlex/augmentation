use itertools::{Itertools, iproduct};

use crate::{
    comps::CompType,
    path::PathProofNode,
    path::{
        instance::{CycleComp, Instance, PseudoCycle},
        utils::complex_cycle_value_base,
        NicePairConfig, PathComp,
    },
    Credit, CreditInv, Node, types::Edge,
};

pub fn check_cycle_merge(instance: &Instance) -> PathProofNode {
    let pc = instance.pseudo_cycle().unwrap();
    let all_edges = instance.all_edges();
    let path_comps = instance.path_nodes().collect_vec();
    let npc = instance.npc();

    let mut cycle_value = pc.value(&path_comps, &all_edges, &npc, &instance);

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
        instance: &Instance
    ) -> Credit {
        self.total_component_value(path_comps, all_edges, npc, instance) - self.total_edge_cost
    }

    fn total_component_value(
        &self,
        path_comps: &Vec<&PathComp>,
        all_edges: &[Edge],
        npc: &NicePairConfig,
        instance: &Instance
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
                        self.comp_value(comp, in_node, out_node, npc, all_edges, instance, lower_complex)
                    }
                    CycleComp::Rem => {
                        instance.context.inv.two_ec_credit(3) // non shortcutable triangle
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

        match comp.comp.comp_type() {
            CompType::Cycle(_) if !comp.used => {
                if nice_pair {
                    instance.context.inv.credits(&comp.comp) + Credit::from_integer(1) // shortcut!
                } else {
                    let in_adj = all_edges.iter().filter(|e| comp.comp.is_adjacent(&e.n1, in_node) || comp.comp.is_adjacent(&e.n2, in_node)).collect_vec();
                    let out_adj = all_edges.iter().filter(|e| comp.comp.is_adjacent(&e.n1, out_node) || comp.comp.is_adjacent(&e.n2, out_node)).collect_vec();

                    let cycle_indices = self.cycle.iter().flat_map(|(_, c, _)| match c{
                        CycleComp::PathComp(idx) => Some(idx),
                        CycleComp::Rem => None,
                    }).cloned().collect_vec();

                    let (upper,lower) = comp.comp.paths_between(in_node, out_node);
                    
                    let local_merge_credits = iproduct!(in_adj,out_adj).filter(|(e1,e2)| 
                    e1.other_idx(comp.path_idx) == e2.other_idx(comp.path_idx) && !cycle_indices.contains(&e2.other_idx(comp.path_idx).unwrap()))
                    .filter(|(e1, e2)| {
                        let n1 = e1.endpoint_at(comp.path_idx).unwrap();
                        let n2 = e2.endpoint_at(comp.path_idx).unwrap();

                        (upper.contains(&n1) && lower.contains(&n2)) || (upper.contains(&n2) && lower.contains(&n1))
                    })
                    .map(|(e1,e2)| { let hit_comp = path_comps.iter().find(|c| c.path_idx == e2.other_idx(comp.path_idx).unwrap()).unwrap();
                        credit_inv.credits(&hit_comp.comp)
                    }).max();
                    
                    if let Some(add) = local_merge_credits {
                        return credit_inv.credits(&comp.comp) + add;
                    } else {
                        return credit_inv.credits(&comp.comp)
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
