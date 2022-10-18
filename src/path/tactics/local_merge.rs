use itertools::Itertools;

use crate::{
    path::{
        proof::PathContext, AugmentedPathInstance, 
        SelectedHitInstance, ZoomedNode,
    },
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
    types::Edge,
    Credit,
};

#[derive(Clone)]
pub struct LocalMergeTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl LocalMergeTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for LocalMergeTactic {
    fn print_stats(&self) {
        println!("Local merge {} / {}", self.num_proofs, self.num_calls);
    }
}

fn merge(
    left: &ZoomedNode,
    right: &ZoomedNode,
    edges_between: &[Edge],
    context: &PathContext,
) -> ProofNode {
    let left_comp = left.get_comp();
    let right_comp = right.get_comp();

    if left_comp.is_complex() && right_comp.is_complex() {
        return ProofNode::new_leaf("Merge two complex components".into(), true);
    }

    let total_comp_credit =
        context.credit_inv.credits(&left_comp) + context.credit_inv.credits(&right_comp);

    if left_comp.is_complex() || right_comp.is_complex() {
        let (_, complex_comp) = if left_comp.is_complex() {
            (left, left_comp)
        } else {
            (right, right_comp)
        };
        let (other, other_comp) = if !left_comp.is_complex() {
            (left, left_comp)
        } else {
            (right, right_comp)
        };

        for buy in edges_between.iter().powerset().filter(|p| p.len() == 2) {
            let mut total_block_merge = total_comp_credit;
            let other1 = other_comp.incident(&buy[0]).unwrap();
            let other2 = other_comp.incident(&buy[1]).unwrap();
            let complex1 = complex_comp.incident(&buy[0]).unwrap();
            let complex2 = complex_comp.incident(&buy[1]).unwrap();

            if other.npc.is_nice_pair(other1, other2) {
                total_block_merge += Credit::from_integer(1)
            }

            let gained_complex_deg = complex_comp.complex_degree_between(&complex1, &complex2);

            total_block_merge += context.credit_inv.complex_black(gained_complex_deg as i64);

            if total_block_merge >= Credit::from_integer(3) {
                // we have to pay for block credit and two edges
                return ProofNode::new_leaf_success(
                    "Local merge to complex".into(),
                    total_block_merge == Credit::from_integer(3),
                );
            }

            if complex_comp.is_adjacent(&complex1, &complex2) && other_comp.is_large() {
                return ProofNode::new_leaf("Merge complex and large to complex!".into(), true);
            }

            if complex_comp.is_adjacent(&complex1, &complex2)
                && !other_comp.is_large()
                && other.npc.is_nice_pair(other1, other2)
            {
                let mut total_complex_merge = total_comp_credit;
                total_complex_merge += Credit::from_integer(1); // gain one credit from nice pair
                total_complex_merge += Credit::from_integer(1); // gain one credit for shortcutting complex
                let created_black_degree = 2 * other_comp.num_edges() + 2;
                if total_complex_merge
                    >= context
                        .credit_inv
                        .complex_black(created_black_degree as i64)
                {
                    // we have to pay for creation of black vertices
                    return ProofNode::new_leaf("Local merge to complex".into(), true);
                }
            }
        }
    } else {
        for buy in edges_between.iter().powerset().filter(|p| p.len() == 2) {
            let l1 = left_comp.incident(&buy[0]).unwrap();
            let l2 = left_comp.incident(&buy[1]).unwrap();
            let r1 = right_comp.incident(&buy[0]).unwrap();
            let r2 = right_comp.incident(&buy[1]).unwrap();

            let mut credits = total_comp_credit - Credit::from_integer(2);

            if left.npc.is_nice_pair(l1, l2) {
                credits += Credit::from_integer(1)
            }
            if right.npc.is_nice_pair(r1, r2) {
                credits += Credit::from_integer(1)
            }

            let req_credits = context
                .credit_inv
                .two_ec_credit(left_comp.num_edges() + right_comp.num_edges());
            if credits >= req_credits {
                return ProofNode::new_leaf_success("Local merge".into(), credits == req_credits);
            }
        }
    }
    ProofNode::new_leaf("Local merge impossible".into(), false)
}

impl Tactic<AugmentedPathInstance, PathContext> for LocalMergeTactic {
    fn action(&mut self, data: &AugmentedPathInstance, context: &PathContext) -> ProofNode {
        self.num_calls += 1;

        let res = data
            .nodes
            .iter()
            .enumerate()
            .tuple_combinations::<(_, _)>()
            .find_map(|((left_idx, left), (right_idx, right))| {
                if left.is_zoomed() && right.is_zoomed() {
                    let left = left.get_zoomed();
                    let right = right.get_zoomed();
                    let edges_between = data.fixed_edges_between(left_idx.into(), right_idx.into());
                    if !edges_between.is_empty() {
                        let mut res = merge(left, right, &edges_between, &context);
                        if res.eval().success() {
                            self.num_proofs += 1;
                            return Some(res);
                        }
                    }
                }
                None
            });

        if res.is_some() {
            res.unwrap()
        } else {
            ProofNode::new_leaf(
                "No local merge found between any two zoomed nodes".into(),
                false,
            )
        }
    }

    fn precondition(&self, data: &AugmentedPathInstance, _context: &PathContext) -> bool {
        data.nodes.iter().filter(|n| n.is_zoomed()).count() >= 2
    }
}

impl Tactic<SelectedHitInstance, PathContext> for LocalMergeTactic {
    fn precondition(&self, data: &SelectedHitInstance, context: &PathContext) -> bool {
        Tactic::<AugmentedPathInstance, PathContext>::precondition(self, &data.instance, context)
    }

    fn action(&mut self, data: &SelectedHitInstance, context: &PathContext) -> ProofNode {
        Tactic::<AugmentedPathInstance, PathContext>::action(self, &data.instance, context)
    }
}
