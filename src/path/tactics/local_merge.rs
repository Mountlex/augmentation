use itertools::Itertools;

use crate::{
    path::PathProofNode,
    path::{proof::Instance, InstanceContext, NicePairConfig, PathComp},
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

    if left_comp.is_complex() && right_comp.is_complex() {
        return PathProofNode::new_leaf("Merge two complex components".into(), true);
    }

    let total_comp_credit = context.inv.credits(left_comp) + context.inv.credits(right_comp);

    if left_comp.is_complex() || right_comp.is_complex() {
        let (_, complex_comp) = if left_comp.is_complex() {
            (left, left_comp)
        } else {
            (right, right_comp)
        };
        let (_, other_comp) = if !left_comp.is_complex() {
            (left, left_comp)
        } else {
            (right, right_comp)
        };

        for buy in edges_between.iter().powerset().filter(|p| p.len() == 2) {
            let mut total_block_merge = total_comp_credit;
            let other1 = other_comp.incident(buy[0]).unwrap();
            let other2 = other_comp.incident(buy[1]).unwrap();
            let complex1 = complex_comp.incident(buy[0]).unwrap();
            let complex2 = complex_comp.incident(buy[1]).unwrap();

            if npc.is_nice_pair(other1, other2) {
                total_block_merge += Credit::from_integer(1)
            }

            let gained_complex_deg = complex_comp.complex_degree_between(&complex1, &complex2);

            total_block_merge += context.inv.complex_black(gained_complex_deg as i64);

            if total_block_merge >= Credit::from_integer(3) {
                // we have to pay for block credit and two edges
                return PathProofNode::new_leaf_success(
                    "Local merge to complex".into(),
                    total_block_merge == Credit::from_integer(3),
                );
            }

            if complex_comp.is_adjacent(&complex1, &complex2) && other_comp.is_large() {
                return PathProofNode::new_leaf("Merge complex and large to complex!".into(), true);
            }

            if complex_comp.is_adjacent(&complex1, &complex2)
                && !other_comp.is_large()
                && npc.is_nice_pair(other1, other2)
            {
                let mut total_complex_merge = total_comp_credit;
                total_complex_merge += Credit::from_integer(1); // gain one credit from nice pair
                total_complex_merge += Credit::from_integer(1); // gain one credit for shortcutting complex
                let created_black_degree = 2 * other_comp.num_edges() + 2;
                if total_complex_merge >= context.inv.complex_black(created_black_degree as i64) {
                    // we have to pay for creation of black vertices
                    return PathProofNode::new_leaf("Local merge to complex".into(), true);
                }
            }
        }
    } else {
        for buy in edges_between.iter().powerset().filter(|p| p.len() == 2) {
            let l1 = left_comp.incident(buy[0]).unwrap();
            let l2 = left_comp.incident(buy[1]).unwrap();
            let r1 = right_comp.incident(buy[0]).unwrap();
            let r2 = right_comp.incident(buy[1]).unwrap();

            let mut credits = total_comp_credit - Credit::from_integer(2);

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

pub fn check_local_merge(instance: &Instance) -> PathProofNode {
    let all_edges = instance.all_edges();
    //let new_edges = instance.last_added_edges();
    let all_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    let res = all_comps
        .iter()
        .tuple_combinations::<(_, _)>()
        // .filter(|(left, right)| {
        //     new_edges.len() != 1 || (new_edges[0].between_path_nodes(left.path_idx, right.path_idx))
        // })
        .find_map(|(left, right)| {
            let edges_between = all_edges
                .iter()
                .filter(|e| e.between_path_nodes(left.path_idx, right.path_idx))
                .cloned()
                .collect_vec();
            if !edges_between.is_empty() {
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
        PathProofNode::new_leaf(
            "No local merge found between any two zoomed nodes".into(),
            false,
        )
    }
}
