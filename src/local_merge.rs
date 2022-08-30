use std::path::PathBuf;

use itertools::{iproduct, Itertools};
use num_rational::Rational64;
use petgraph::{algo::connected_components, visit::EdgeFiltered};
use rayon::prelude::*;

use crate::{
    bridges::{is_complex, ComplexCheckResult},
    comps::{Component, ComponentType, CreditInvariant, EdgeType, Graph, Node},
    edges_of_type, merge_components_to_base,
    proof_tree::{ProofNode, Tree},
    Credit,
};

pub struct TreeCaseProof<C> {
    leaf_comps: Vec<ComponentType>,
    comps: Vec<ComponentType>,
    credit_inv: C,
    start_depth: usize,
}

impl<C: CreditInvariant + Sync> TreeCaseProof<C> {
    pub fn new(
        leaf_comps: Vec<ComponentType>,
        comps: Vec<ComponentType>,
        credit_inv: C,
        start_depth: usize,
    ) -> Self {
        TreeCaseProof {
            leaf_comps,
            comps,
            credit_inv,
            start_depth,
        }
    }

    pub fn prove(&self, output_dir: PathBuf) {
        std::fs::create_dir_all(&output_dir).expect("Unable to create directory");

        // Enumerate every graph combination and prove merge
        let combinations: Vec<(Component, Component)> = iproduct!(
            self.leaf_comps.iter().flat_map(|c| c.components()),
            self.comps.iter().flat_map(|c| c.components())
        )
        .collect_vec();
        combinations.into_par_iter().for_each(|(left, right)| {
            log::info!("Proving local merge between {} and {} ...", left, right);

            let left_graph = left.graph();

            let mut root = ProofNode::new_all("Proof".into());
            let result = self.prove_local_merge(
                left_graph.clone(),
                vec![&left],
                right.clone(),
                self.start_depth,
                &mut root,
            );

            let filename = if result {
                log::info!("✔️ Proved local merge between {} and {} ", left, right);
                output_dir.join(format!(
                    "proof_{}-{}.txt",
                    left.short_name(),
                    right.short_name()
                ))
            } else {
                log::warn!("❌ Disproved local merge between {} and {} ", left, right);
                output_dir.join(format!(
                    "wrong_proof_{}-{}.txt",
                    left.short_name(),
                    right.short_name()
                ))
            };

            let mut buf = String::new();
            root.eval();
            root.print_tree(&mut buf, 0).expect("Unable to format tree");
            std::fs::write(filename, buf).expect("Unable to write file");
        });
    }

    fn prove_local_merge(
        &self,
        left_graph: Graph,
        left_comps: Vec<&Component>,
        right_comp: Component,
        current_depth: usize,
        p_node: &mut ProofNode,
    ) -> bool {
        // Build combined graph and update node indices
        let (graph, mut nodes) = merge_components_to_base(left_graph, vec![right_comp]);
        let right_comp = nodes.remove(0);
        let right_comp_ref = &right_comp;

        let mut proof_node = ProofNode::new_all(format!(
            "Local merge between {} and {}",
            left_comps.iter().map(|c| format!("{}", c)).join(", "),
            right_comp
        ));

        let mut graph_components = left_comps;
        let last_comp = graph_components.last().unwrap().clone();
        graph_components.push(&right_comp);

        // Enumerate all possible matchings (adversarial)
        for left_matched in last_comp.possible_matchings() {
            let right_iter: Vec<Vec<u32>> = match right_comp_ref {
                Component::Cycle(g) => g.nodes().permutations(3).map(|p| p).collect(),
                _ => right_comp_ref.possible_matchings(),
            };
            'match_loop: for perm in right_iter {
                // Compute edges of matching
                let matching: Vec<(u32, u32)> = left_matched
                    .iter()
                    .zip(perm.into_iter())
                    .map(|(l, r)| (*l, r))
                    .collect();

                let mut matching_node = ProofNode::new_any(format!("Matching {:?}", matching));

                let mut graph_with_matching = graph.clone();
                for (m1, m2) in &matching {
                    graph_with_matching.add_edge(*m1, *m2, EdgeType::Buyable);
                }

                // Proof #1
                if prove_via_direct_merge(
                    &graph_with_matching,
                    graph_components.clone(),
                    self.credit_inv.clone(),
                    &mut matching_node,
                ) {
                    proof_node.add_child(matching_node);
                    continue 'match_loop;
                }

                // Proof #2 check if any component is contractible (TODO check combinations)
                for comp in &graph_components {
                    if self.prove_via_contractable_arguments(
                        comp,
                        &graph_with_matching,
                        &graph_components,
                        &mut matching_node,
                    ) {
                        proof_node.add_child(matching_node);
                        continue 'match_loop;
                    }
                }

                // Proof #3
                if self.prove_via_contractable_arguments(
                    &right_comp,
                    &graph_with_matching,
                    &graph_components,
                    &mut matching_node,
                ) {
                    proof_node.add_child(matching_node);
                    continue 'match_loop;
                }

                // Proof #4
                if self.prove_via_enumerating_neighbors(
                    &graph_with_matching,
                    &graph_components,
                    current_depth,
                    &mut matching_node,
                ) {
                    proof_node.add_child(matching_node);
                    continue 'match_loop;
                }

                // If we reach here, no proof was successful for this matching!
                proof_node.add_child(matching_node);
                p_node.add_child(proof_node);
                return false;
            }
        }
        p_node.add_child(proof_node);
        true

        // If we found shortcuts for every matching, this combination is valid
    }

    fn prove_via_enumerating_neighbors(
        &self,
        graph: &Graph,
        graph_components: &Vec<&Component>,
        current_depth: usize,
        proof_node: &mut ProofNode,
    ) -> bool {
        if current_depth == 0 {
            proof_node.add_child(ProofNode::new_leaf(
                format!("Max depth ({}) reached!", self.start_depth),
                false,
            ));
            return false;
        }

        let mut add_comp_node =
            ProofNode::new_all("Larger merge with any component on the right".into());

        let mut success = true;

        for next in self.comps.iter().flat_map(|c| c.components()) {
            if graph_components.len() == 2 {
                match (graph_components[0], graph_components[1], &next) {
                    (Component::Cycle(g0), Component::Cycle(g1), Component::Cycle(g2))
                        if g0.edge_count() == 5 && g1.edge_count() == 4 && g2.edge_count() == 5 =>
                    {
                        continue
                    }
                    _ => (),
                }
            }

            if !self.prove_local_merge(
                graph.clone(),
                graph_components.clone(),
                next.clone(),
                current_depth - 1,
                &mut add_comp_node,
            ) {
                success = false;
                break;
            }
        }

        proof_node.add_child(add_comp_node);
        success
    }

    fn prove_via_contractable_arguments(
        &self,
        comp: &Component,
        graph: &Graph,
        graph_components: &Vec<&Component>,
        proof_node: &mut ProofNode,
    ) -> bool {
        if matches!(comp, Component::Cycle(g) if g.node_count() == 6) {
            // comp is H
            let mut necessary_edges = 0;
            let mut inner_vertices = vec![];
            for v in comp.graph().nodes() {
                if graph.neighbors(v).all(|u| comp.graph().contains_node(u)) {
                    // v has only neighbors in H, i.e. no incident matching edges
                    inner_vertices.push(v);
                    necessary_edges += 2;
                }
            }

            for edge in inner_vertices.iter().combinations(2) {
                let u = edge[0];
                let v = edge[1];

                if graph.contains_edge(*u, *v) {
                    necessary_edges -= 1;
                }
            }

            if necessary_edges == 6 {
                let mut cont_node = ProofNode::new_all(format!(
                    "Component {}-contractible! Adding single edges now and checking again",
                    necessary_edges as f32 / 6 as f32
                ));

                let mut verify = true;
                for edge in inner_vertices.iter().combinations(2) {
                    let u = edge[0];
                    let v = edge[1];

                    let mut graph_with_added_edge = graph.clone();
                    graph_with_added_edge.add_edge(*u, *v, EdgeType::Buyable);

                    let mut edge_node = ProofNode::new_any(format!("Added edge {}-{}", u, v));

                    let res = prove_via_direct_merge(
                        &graph_with_added_edge,
                        graph_components.clone(),
                        self.credit_inv.clone(),
                        &mut edge_node,
                    );
                    cont_node.add_child(edge_node);
                    if !res {
                        verify = false;
                        break;
                    }
                }
                proof_node.add_child(cont_node);

                return verify;
            }

            proof_node.add_child(ProofNode::new_leaf(
                format!("No contractible 6-cycle!"),
                false,
            ));
        }
        // if comp is no 6-cycle, we don't add something to the tree.
        return false;
    }
}

fn prove_via_direct_merge<C: CreditInvariant>(
    graph: &Graph,
    graph_components: Vec<&Component>,
    credit_inv: C,
    proof_node: &mut ProofNode,
) -> bool {
    let sellable = edges_of_type(graph, EdgeType::Sellable);
    let buyable = edges_of_type(graph, EdgeType::Buyable);

    let total_component_credits = graph_components.iter().map(|c| credit_inv.credits(c)).sum();

    let result = find_feasible_merge(
        graph,
        buyable.into_iter().powerset().filter(|p| p.len() >= 1),
        sellable.into_iter().powerset(),
        total_component_credits,
        credit_inv.clone(),
        graph_components
            .iter()
            .any(|c| matches!(c, Component::Complex(_, _, _))),
    );

    match result {
        MergeResult::FeasibleLarge(merge) => {
            proof_node.add_child(ProofNode::new_leaf(format!("Direct merge to large possible [bought = {:?}, sold = {:?}, credits: {} + {} - {} >= {}]", merge.bought_edges, merge.sold_edges, total_component_credits, merge.sold_edges.len(), merge.bought_edges.len(), merge.new_comp_credit), true));
            true
        }
        MergeResult::FeasibleComplex(merge) => {
            proof_node.add_child(ProofNode::new_leaf(format!("Direct merge to complex possible [bought = {:?}, sold = {:?}, credits: {} + {} - {} >= {}]", merge.bought_edges, merge.sold_edges, total_component_credits, merge.sold_edges.len(), merge.bought_edges.len(), merge.new_comp_credit), true));
            true
        }
        MergeResult::Impossible => {
            proof_node.add_child(ProofNode::new_leaf(
                format!(
                    "Direct merge impossible [available credits: {}]",
                    total_component_credits
                ),
                false,
            ));
            false
        }
    }
}

pub struct FeasibleMerge {
    bought_edges: Vec<(Node, Node)>,
    sold_edges: Vec<(Node, Node)>,
    new_comp_credit: Credit,
}

pub enum MergeResult {
    FeasibleLarge(FeasibleMerge),
    FeasibleComplex(FeasibleMerge),
    Impossible,
}

pub fn find_feasible_merge<'a, B, S, C: CreditInvariant>(
    graph: &Graph,
    buy_iter: B,
    sell_iter: S,
    total_component_credits: Credit,
    credit_inv: C,
    one_is_complex: bool,
) -> MergeResult
where
    B: Iterator<Item = Vec<(u32, u32)>> + Clone,
    S: Iterator<Item = Vec<(u32, u32)>>,
{
    for sell in sell_iter {
        let sell_credits = Rational64::from_integer(sell.len() as i64);
        let total_plus_sell = total_component_credits + sell_credits;

        for buy in buy_iter.clone() {
            let buy_credits = Rational64::from_integer(buy.len() as i64);

            let check_graph = EdgeFiltered::from_fn(graph, |(v1, v2, t)| {
                if t == &EdgeType::Sellable && sell.contains(&(v1, v2)) || sell.contains(&(v2, v1))
                {
                    false
                } else if t == &EdgeType::Buyable
                    && !buy.contains(&(v1, v2))
                    && !buy.contains(&(v2, v1))
                {
                    false
                } else {
                    true
                }
            });

            if !one_is_complex {
                if total_plus_sell - buy_credits < credit_inv.large() {
                    continue;
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
                        * credit_inv.complex_block()
                        + credit_inv.complex_black(black_deg as i64)
                        + credit_inv.complex_comp();

                    if total_plus_sell - buy_credits >= new_credits {
                        //dbg!(bridges);
                        //dbg!(num_blocks);
                        //dbg!(black_vertices);
                        //dbg!(black_deg);

                        return MergeResult::FeasibleComplex(FeasibleMerge {
                            bought_edges: buy.clone(),
                            sold_edges: sell.clone(),
                            new_comp_credit: new_credits,
                        });
                    }
                }
                ComplexCheckResult::NoBridges => {
                    if total_plus_sell - buy_credits >= credit_inv.large() {
                        return MergeResult::FeasibleLarge(FeasibleMerge {
                            bought_edges: buy.clone(),
                            sold_edges: sell.clone(),
                            new_comp_credit: credit_inv.large(),
                        });
                    }
                }
                ComplexCheckResult::BlackLeaf => continue,
                ComplexCheckResult::NotConnected | ComplexCheckResult::Empty => continue,
            }
        }
    }
    return MergeResult::Impossible;
}
