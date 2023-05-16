use itertools::Itertools;

use crate::{
    path::PathProofNode,
    path::{
        instance::{Instance, InstanceContext},
        NicePairConfig, PathComp,
    },
    types::Edge,
    Credit,
};

fn merge(
    left: &PathComp,
    right: &PathComp,
    edges_between: &[Edge],
    npc: &NicePairConfig,
    context: &InstanceContext,
) -> PathProofNode {
    let left_comp = &left.comp;
    let right_comp = &right.comp;

    let total_comp_credit = context.inv.credits(left_comp) + context.inv.credits(right_comp);

    for buy in edges_between.iter().powerset().filter(|p| p.len() == 2) {
        // at most one credit gaining edge
        if buy[0].cost == Credit::from_integer(1) || buy[1].cost == Credit::from_integer(1) {
            let buy_cost: Credit = buy.iter().map(|e| e.cost).sum();
            //assert_eq!(buy_cost, Credit::from(2));
            let l1 = left_comp.incident(buy[0]).unwrap();
            let l2 = left_comp.incident(buy[1]).unwrap();
            let r1 = right_comp.incident(buy[0]).unwrap();
            let r2 = right_comp.incident(buy[1]).unwrap();

            let mut credits = total_comp_credit - buy_cost;

            if npc.is_nice_pair(l1, l2) {
                credits += Credit::from_integer(1)
            }
            if npc.is_nice_pair(r1, r2) {
                credits += Credit::from_integer(1)
            }

            let req_credits = context
                .inv
                .two_ec_credit(left_comp.num_edges() + right_comp.num_edges());
            if credits >= req_credits {
                return PathProofNode::new_leaf_success(
                    "Local merge".into(),
                    credits == req_credits,
                );
            }
        }
    }

    PathProofNode::new_leaf("Local merge impossible".into(), false)
}

fn merge2(
    left: &PathComp,
    middle: &PathComp,
    right: &PathComp,
    edges_between1: &[Edge],
    edges_between2: &[Edge],
    npc: &NicePairConfig,
    context: &InstanceContext,
) -> PathProofNode {
    let left_comp = &left.comp;
    let middle_comp = &middle.comp;

    let right_comp = &right.comp;

    let total_comp_credit = context.inv.credits(left_comp)
        + context.inv.credits(middle_comp)
        + context.inv.credits(right_comp);

    for buy1 in edges_between1.iter().powerset().filter(|p| p.len() == 2) {
        for buy2 in edges_between2.iter().powerset().filter(|p| p.len() == 2) {
            if buy1
                .iter()
                .chain(buy2.iter())
                .filter(|e| e.cost < Credit::from_integer(1))
                .count()
                <= 1
            {
                let buy_cost: Credit = buy1.iter().map(|e| e.cost).sum::<Credit>()
                    + buy2.iter().map(|e| e.cost).sum::<Credit>();
                //assert_eq!(buy_cost, Credit::from(2));
                let l1 = left_comp.incident(buy1[0]).unwrap();
                let l2 = left_comp.incident(buy1[1]).unwrap();
                let ml1 = middle_comp.incident(buy1[0]).unwrap();
                let ml2 = middle_comp.incident(buy1[1]).unwrap();

                let mr1 = middle_comp.incident(buy2[0]).unwrap();
                let mr2 = middle_comp.incident(buy2[1]).unwrap();
                let r1 = right_comp.incident(buy2[0]).unwrap();
                let r2 = right_comp.incident(buy2[1]).unwrap();

                let mut credits = total_comp_credit - buy_cost;

                if npc.is_nice_pair(l1, l2) {
                    credits += Credit::from_integer(1)
                }
                if npc.is_nice_pair(ml1, ml2) || npc.is_nice_pair(mr1, mr2) {
                    credits += Credit::from_integer(1)
                }
                if npc.is_nice_pair(r1, r2) {
                    credits += Credit::from_integer(1)
                }

                let req_credits = context.inv.two_ec_credit(
                    left_comp.num_edges() + middle_comp.num_edges() + right_comp.num_edges(),
                );
                if credits >= req_credits {
                    return PathProofNode::new_leaf_success(
                        "Local merge".into(),
                        credits == req_credits,
                    );
                }
            }
        }
    }

    PathProofNode::new_leaf("Local merge impossible".into(), false)
}

pub fn check_local_merge(instance: &Instance) -> PathProofNode {
    let all_edges = instance.all_edges();
    //let last_added_edge = instance.last_single_edge();
    let all_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    let res = all_comps
        .iter()
        .tuple_combinations::<(_, _)>()
        // .filter(|(left, right)| {
        //     if let Some(edge) = last_added_edge {
        //         edge.between_path_nodes(left.path_idx, right.path_idx)
        //     } else {
        //         true
        //     }
        // })
        .find_map(|(left, right)| {
            let edges_between = all_edges
                .iter()
                .filter(|e| e.between_path_nodes(left.path_idx, right.path_idx))
                .cloned()
                .collect_vec();
            if edges_between.len() >= 2 {
                let mut res = merge(left, right, &edges_between, &npc, &instance.context);
                if res.eval().success() {
                    return Some(res);
                }
            }
            None
        });

    if res.is_some() {
        res.unwrap()
    } else {
        let res = all_comps
            .iter()
            .permutations(3)
            // .filter(|(left, right)| {
            //     if let Some(edge) = last_added_edge {
            //         edge.between_path_nodes(left.path_idx, right.path_idx)
            //     } else {
            //         true
            //     }
            // })
            .find_map(|perm| {
                let left = perm[0];
                let middle = perm[1];
                let right = perm[2];
                let edges_between1 = all_edges
                    .iter()
                    .filter(|e| e.between_path_nodes(left.path_idx, middle.path_idx))
                    .cloned()
                    .collect_vec();
                let edges_between2 = all_edges
                    .iter()
                    .filter(|e| e.between_path_nodes(middle.path_idx, right.path_idx))
                    .cloned()
                    .collect_vec();
                if edges_between1.len() >= 2 && edges_between2.len() >= 2 {
                    let mut res = merge2(
                        left,
                        middle,
                        right,
                        &edges_between1,
                        &edges_between2,
                        &npc,
                        &instance.context,
                    );
                    if res.eval().success() {
                        return Some(res);
                    }
                }
                None
            });

        if res.is_some() {
            res.unwrap()
        } else {
            PathProofNode::new_leaf(
                "No local merge found between any two zoomed nodes".into(),
                false,
            )
        }
    }
}
