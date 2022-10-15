use itertools::Itertools;
use petgraph::{algo::connected_components, visit::EdgeFiltered};

use crate::{
    bridges::{is_complex, ComplexCheckResult},
    comps::{edges_of_type, EdgeType},
    path::{
        proof::PathContext, utils::get_local_merge_graph, AugmentedPathInstance, Pidx,
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
    do_complex: bool,
}

impl LocalMergeTactic {
    pub fn new(do_complex: bool) -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
            do_complex,
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
    do_complex: bool,
) -> ProofNode {
    let left_comp = left.get_comp();
    let right_comp = right.get_comp();

    let total_comp_credit =
        context.credit_inv.credits(&left_comp) + context.credit_inv.credits(&right_comp);

    if left_comp.is_complex() || right_comp.is_complex() {
        if !do_complex {
            return ProofNode::new_leaf("No complex local merge".into(), false);
        }

        let graph_with_matching = get_local_merge_graph(
            &left_comp,
            &right_comp,
            &edges_between.iter().map(|e| e.to_tuple()).collect_vec(),
        );

        for sell in edges_of_type(&graph_with_matching, EdgeType::Sellable)
            .into_iter()
            .powerset()
            .filter(|s| s.len() <= 2)
        {
            let sell_credits = Credit::from_integer(sell.len() as i64);
            let mut total_plus_sell = total_comp_credit + sell_credits;

            for buy in edges_between
                .iter()
                .powerset()
                .filter(|p| !p.is_empty())
            {
                let buy_credits = Credit::from_integer(buy.len() as i64);

                let check_graph = EdgeFiltered::from_fn(&graph_with_matching, |(v1, v2, t)| {
                    if t == &EdgeType::Sellable && sell.contains(&(v1, v2))
                        || sell.contains(&(v2, v1))
                    {
                        false
                    } else if t == &EdgeType::Buyable
                        && !buy.contains(&&Edge::new(v1, Pidx::Last, v2, Pidx::Last))
                    {
                        false
                    } else {
                        true
                    }
                });

                if buy.len() == 2 && !(left_comp.is_complex() && right_comp.is_complex()) {
                    let l1 = left_comp.incident(&buy[0]).unwrap();
                    let l2 = left_comp.incident(&buy[1]).unwrap();
                    let r1 = right_comp.incident(&buy[0]).unwrap();
                    let r2 = right_comp.incident(&buy[1]).unwrap();

                    if !left_comp.is_adjacent(&l1, &l2) && left.npc.is_nice_pair(l1, l2) {
                        total_plus_sell += Credit::from_integer(1)
                    }
                    if !right_comp.is_adjacent(&r1, &r2) && right.npc.is_nice_pair(r1, r2) {
                        total_plus_sell += Credit::from_integer(1)
                    }
                }

                let white_vertices =
                    vec![left_comp.white_nodes(), right_comp.white_nodes()].concat();

                match is_complex(&check_graph, &white_vertices, false) {
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
                        let req_credits = context
                            .credit_inv
                            .two_ec_credit(left_comp.num_edges() + right_comp.num_edges());
                        if total_plus_sell - buy_credits >= req_credits {
                            return ProofNode::new_leaf_success(
                                "Local merge".into(),
                                total_plus_sell - buy_credits == req_credits,
                            );
                        }
                    }
                    ComplexCheckResult::BlackLeaf => continue,
                    ComplexCheckResult::NotConnected | ComplexCheckResult::Empty => continue,
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
                        let mut res = merge(left, right, &edges_between, &context, self.do_complex);
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
