use itertools::Itertools;
use petgraph::{algo::connected_components, visit::EdgeFiltered};

use crate::{
    bridges::{is_complex, ComplexCheckResult},
    comps::{edges_of_type, CreditInvariant, EdgeType},
    path::{
        proof::{ProofContext, Statistics, Tactic},
        utils::get_local_merge_graph,
        AugmentedPathInstance, SelectedHitInstance, ZoomedNode,
    },
    proof_tree::ProofNode,
    types::Edge,
    Credit,
};

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
    context: &ProofContext,
) -> ProofNode {
    let left_comp = left.get_comp();
    let right_comp = right.get_comp();

    let graph_with_matching = get_local_merge_graph(
        &left_comp,
        &right_comp,
        &edges_between.iter().map(|e| (e.0, e.1)).collect_vec(),
    );

    let total_comp_credit =
        context.credit_inv.credits(&left_comp) + context.credit_inv.credits(&right_comp);

    if left_comp.is_complex() || right_comp.is_complex() {
        for sell in edges_of_type(&graph_with_matching, EdgeType::Sellable)
            .into_iter()
            .powerset()
        {
            let sell_credits = Credit::from_integer(sell.len() as i64);
            let mut total_plus_sell = total_comp_credit + sell_credits;

            for buy in edges_between
                .iter()
                .cloned()
                .powerset()
                .filter(|p| !p.is_empty())
            {
                let buy_credits = Credit::from_integer(buy.len() as i64);

                let check_graph = EdgeFiltered::from_fn(&graph_with_matching, |(v1, v2, t)| {
                    if t == &EdgeType::Sellable && sell.contains(&(v1, v2))
                        || sell.contains(&(v2, v1))
                    {
                        false
                    } else if t == &EdgeType::Buyable && !buy.contains(&Edge(v1, v2)) {
                        false
                    } else {
                        true
                    }
                });

                if buy.len() == 2 && !(left_comp.is_complex() && right_comp.is_complex()) {
                    let l1 = buy[0].0;
                    let r1 = buy[0].1;
                    let l2 = buy[1].0;
                    let r2 = buy[1].1;

                    if !left_comp.is_adjacent(l1, l2) && left.npc.is_nice_pair(l1, l2) {
                        total_plus_sell += Credit::from_integer(1)
                    }
                    if !right_comp.is_adjacent(r1, r2) && right.npc.is_nice_pair(r1, r2) {
                        total_plus_sell += Credit::from_integer(1)
                    }
                }

                match is_complex(&check_graph) {
                    ComplexCheckResult::Complex(bridges, black_vertices) => {
                        let blocks_graph = EdgeFiltered::from_fn(&check_graph, |(v, u, _)| {
                            !bridges.contains(&(v, u)) && !bridges.contains(&(u, v))
                        });
                        let num_blocks = connected_components(&blocks_graph) - black_vertices.len();
                        let black_deg: usize = black_vertices
                            .iter()
                            .map(|v| bridges.iter().filter(|(a, b)| a == v || b == v).count())
                            .sum();
                        let new_credits = Credit::from_integer(num_blocks as i64)
                            * context.credit_inv.complex_block()
                            + context.credit_inv.complex_black(black_deg as i64)
                            + context.credit_inv.complex_comp();

                        if total_plus_sell - buy_credits >= new_credits {
                            return ProofNode::new_leaf_success(
                                "Local merge to complex".into(),
                                total_plus_sell - buy_credits == new_credits,
                            );
                        }
                    }
                    ComplexCheckResult::NoBridges => {
                        if left_comp.is_c3() && right_comp.is_c3() {
                            if total_plus_sell - buy_credits >= context.credit_inv.two_ec_credit(6)
                            {
                                return ProofNode::new_leaf_success(
                                    "Local merge to c6".into(),
                                    total_plus_sell - buy_credits
                                        == context.credit_inv.two_ec_credit(6),
                                );
                            }
                        } else {
                            if total_plus_sell - buy_credits >= context.credit_inv.large() {
                                return ProofNode::new_leaf_success(
                                    "Local merge to large".into(),
                                    total_plus_sell - buy_credits == context.credit_inv.large(),
                                );
                            }
                        }
                    }
                    ComplexCheckResult::BlackLeaf => continue,
                    ComplexCheckResult::NotConnected | ComplexCheckResult::Empty => continue,
                }
            }
        }
    } else {
        for buy in edges_between.iter().powerset().filter(|p| p.len() == 2) {
            let l1 = buy[0].0;
            let r1 = buy[0].1;
            let l2 = buy[1].0;
            let r2 = buy[1].1;

            let mut credits = total_comp_credit - Credit::from_integer(2);

            if left.npc.is_nice_pair(l1, l2) {
                credits += Credit::from_integer(1)
            }
            if right.npc.is_nice_pair(r1, r2) {
                credits += Credit::from_integer(1)
            }

            if left_comp.is_c3() && right_comp.is_c3() {
                if credits >= context.credit_inv.two_ec_credit(6) {
                    return ProofNode::new_leaf_success(
                        "Local merge to c6".into(),
                        credits == context.credit_inv.two_ec_credit(6),
                    );
                }
            } else {
                if credits >= context.credit_inv.large() {
                    return ProofNode::new_leaf_success(
                        "Local merge to large".into(),
                        credits == context.credit_inv.large(),
                    );
                }
            }
        }
    }
    ProofNode::new_leaf("Local merge impossible".into(), false)
}

impl Tactic<AugmentedPathInstance> for LocalMergeTactic {
    fn action(&mut self, data: &AugmentedPathInstance, context: &ProofContext) -> ProofNode {
        self.num_calls += 1;

        let res = data
            .path
            .nodes
            .iter()
            .enumerate()
            .tuple_combinations::<(_, _)>()
            .find_map(|((left_idx, left), (right_idx, right))| {
                if left.is_zoomed() && right.is_zoomed() {
                    let left = left.get_zoomed();
                    let right = right.get_zoomed();
                    let edges_between = data.fixed_edges_between(left_idx, right_idx);
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

    fn precondition(&self, data: &AugmentedPathInstance, _context: &ProofContext) -> bool {
        data.path.nodes.iter().filter(|n| n.is_zoomed()).count() >= 2
    }
}

impl Tactic<SelectedHitInstance> for LocalMergeTactic {
    fn precondition(&self, data: &SelectedHitInstance, context: &ProofContext) -> bool {
        Tactic::<AugmentedPathInstance>::precondition(self, &data.instance, context)
    }

    fn action(&mut self, data: &SelectedHitInstance, context: &ProofContext) -> ProofNode {
        Tactic::<AugmentedPathInstance>::action(self, &data.instance, context)
    }
}
