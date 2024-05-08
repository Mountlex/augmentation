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

/// Check whether any two or three components can be merged together to a single component. This gives us progress, because we reduce the total number of components.
pub fn check_local_merge(instance: &Instance) -> PathProofNode {
    // get information about the instance
    let all_edges = instance.all_inter_comp_edges();
    let all_comps = instance.path_nodes().cloned().collect_vec();
    let npc = instance.npc();

    let res = all_comps
        .iter()
        .tuple_combinations::<(_, _)>() // we iterate through all tuple combinations of components in our current nice path
        .find_map(|(left, right)| {
            // compute all edges which are between left and right. For this, we use the path_idx attribute of left and right, which gives use the index of the component in the nice path (i.e. the last component has idx 0 ...). Since every edge also knowns between which two indices it lies, we can simply filter the list of edges.
            let edges_between = all_edges
                .iter()
                .filter(|e| e.between_path_nodes(left.path_idx, right.path_idx))
                .cloned()
                .collect_vec();
            if edges_between.len() >= 2 {
                // if there are less than 2 edges, we cannot merge. If there are at least 2 edge, call merge.
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
        // if we reach here, no merge between two components was possible. Now we essentially do the same thing as before, but this time for every three components instead of only two.
        let res = all_comps.iter().permutations(3).find_map(|perm| {
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

fn merge(
    left: &PathComp,
    right: &PathComp,
    edges_between: &[Edge],
    npc: &NicePairConfig,
    context: &InstanceContext,
) -> PathProofNode {
    let left_comp = &left.comp;
    let right_comp = &right.comp;

    // the total credit of the components (e.g. a C4 has 4*c, a Large has 2). This is defined by this credits method.
    let total_comp_credit = context.inv.credits(left_comp) + context.inv.credits(right_comp);

    // iterate through all possible subsets of edges between left and right. Those we want to buy
    for buy in edges_between.iter().powerset().filter(|p| p.len() == 2) {
        // ignore the comment below
        // if buy[0].cost == Credit::from_integer(1) || buy[1].cost == Credit::from_integer(1) { // at most one credit gaining edge

        // compute the cost of buying the edges (should be always equal to 2 actually, unless we introduce some new ideas)
        let buy_cost: Credit = buy.iter().map(|e| e.cost).sum();

        // compute the nodes of the left and right component which are incident to the edges we buy.
        let l1 = left_comp.incident(buy[0]).unwrap();
        let l2 = left_comp.incident(buy[1]).unwrap();
        let r1 = right_comp.incident(buy[0]).unwrap();
        let r2 = right_comp.incident(buy[1]).unwrap();

        let mut credits = total_comp_credit - buy_cost;

        // check if we can shortcut left or right. If yes, we gain one credit, because we can sell an edge.
        if npc.is_nice_pair(l1, l2) {
            credits += Credit::from_integer(1)
        }
        if npc.is_nice_pair(r1, r2) {
            credits += Credit::from_integer(1)
        }

        // Right now, every merge should result into a large component, which needs a credit of 2. so req_credits should always be 2.
        let req_credits = context
            .inv
            .two_ec_credit(left_comp.num_edges() + right_comp.num_edges());

        // we finally need to check whether we have enough credits. If yes, we succeeded.
        if credits >= req_credits {
            return PathProofNode::new_leaf_success("Local merge".into(), credits == req_credits);
        }
        //}
    }

    PathProofNode::new_leaf("Local merge impossible".into(), false)
}

// this method does the same as merge but for three components: left - middle - right.
// The only thing which changes is that we have to enumerate edges between left and middle and middle and right at the same time, to get all combinations.
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
            let buy_cost: Credit = buy1.iter().map(|e| e.cost).sum::<Credit>()
                + buy2.iter().map(|e| e.cost).sum::<Credit>();
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

    // if we reach here, not merge was possible.
    PathProofNode::new_leaf("Local merge impossible".into(), false)
}
