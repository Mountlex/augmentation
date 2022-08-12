use itertools::{iproduct, Itertools};
use num_rational::Rational64;
use petgraph::visit::{EdgeFiltered, IntoNeighbors};
use rayon::prelude::*;
use std::fmt::Display;

use crate::{
    bridges::no_bridges_and_connected,
    comps::{six_cycle, Component, CreditInvariant, EdgeType, Graph, Node},
    edges_of_type, merge_components_to_base, Credit,
};




pub struct TreeCaseProof<C> {
    comps: Vec<Component>,
    credit_inv: C,
    start_depth: usize,
}

impl<C: CreditInvariant> TreeCaseProof<C> {
    pub fn new(comps: Vec<Component>, credit_inv: C, start_depth: usize) -> Self {
        TreeCaseProof {
            comps,
            credit_inv,
            start_depth,
        }
    }

    pub fn prove(&self) {
        // Enumerate every graph combination and prove merge
        let temp = vec![six_cycle()];
        let combinations: Vec<(&Component, &Component)> =
            iproduct!(&self.comps, &temp).collect_vec();
        combinations.into_iter().for_each(|(left, right)| {
            log::info!("Proving local merge between {} and {} ...", left, right);
            let left_graph = left.graph();
            if self.prove_local_merge(
                left_graph.clone(),
                vec![&left],
                right.clone(),
                self.start_depth,
            ) {
                log::info!("✔️ Proved local merge between {} and {} ", left, right);
            } else {
                log::warn!("❌ Disproved local merge between {} and {} ", left, right);
            }
        });
    }

    fn prove_local_merge(
        &self,
        left_graph: Graph,
        left_comps: Vec<&Component>,
        right_comp: Component,
        depth: usize,
    ) -> bool {
        // Build combined graph and update node indices
        let (graph, mut nodes) = merge_components_to_base(left_graph, vec![right_comp]);
        let right_comp = nodes.remove(0);
        let right_comp_ref = &right_comp;

        let mut graph_components = left_comps;
        let last_comp = graph_components.last().unwrap().clone();
        graph_components.push(&right_comp);

        // Enumerate all possible matchings (adversarial)
        for left_matched in last_comp
            .graph()
            .nodes()
            .powerset()
            .filter(|p| p.len() == 3)
        {
            let right_iter: Vec<Vec<u32>> = match right_comp_ref {
                Component::Simple(g) => g.nodes().permutations(3).map(|p| p).collect(),
                Component::Large(g) => vec![g.nodes().collect()],
                Component::Complex(g) => vec![g.nodes().collect()],
            };
            'match_loop: for perm in right_iter {
                // Compute edges of matching

                let matching = Matching {
                    edges: left_matched
                        .iter()
                        .zip(perm.into_iter())
                        .map(|(l, r)| (*l, r))
                        .collect(),
                    graph_nodes: vec![
                        last_comp.graph().nodes().collect(),
                        right_comp_ref.graph().nodes().collect(),
                    ],
                };

                let mut graph_with_matching = graph.clone();
                for (m1, m2) in &matching.edges {
                    graph_with_matching.add_edge(*m1, *m2, EdgeType::Buyable);
                }

                let proved = find_local_merge_with_matching(
                    &graph_with_matching,
                    graph_components.clone(),
                    self.credit_inv.clone(),
                );

                if !proved {
                    log::trace!(
                        "   Couldn't find local merge with matching edges {}",
                        matching
                    );

                    

                    if matches!(last_comp, Component::Simple(g) if g.node_count() == 6) {
                        println!("six cycle");

                        // last_comp is H
                        let mut necessary_edges = 0;
                        let mut inner_vertices = vec![];
                        for v in last_comp.graph().nodes() {
                            if graph_with_matching
                                .neighbors(v)
                                .all(|u| last_comp.graph().contains_node(u))
                            {
                                // v has only neighbors in H, i.e. no incident matching edges
                                inner_vertices.push(v);
                                necessary_edges += 2;
                            }
                        }

                        for edge in inner_vertices.iter().combinations(2) {
                            let u = edge[0];
                            let v = edge[1];

                            if graph_with_matching.contains_edge(*u, *v) {
                                necessary_edges -= 1;
                            }
                        }

                        if necessary_edges == 6 {
                            dbg!(&inner_vertices);

                            if inner_vertices.iter().combinations(2).all(|edge| {
                                let u = edge[0];
                                let v = edge[1];

                                let mut graph_with_added_edge = graph_with_matching.clone();
                                graph_with_added_edge.add_edge(*u, *v, EdgeType::Buyable);

                                find_local_merge_with_matching(
                                    &graph_with_added_edge,
                                    graph_components.clone(),
                                    self.credit_inv.clone(),
                                )
                            }) {
                                continue 'match_loop;
                            }
                        }
                    }

                    if depth == 0 {
                        return false;
                    }

                    for next in &self.comps {
                        if !self.prove_local_merge(
                            graph_with_matching.clone(),
                            graph_components.clone(),
                            next.clone(),
                            depth - 1,
                        ) {
                            return false;
                        }
                    }
                }
            }
        }

        true

        // If we found shortcuts for every matching, this combination is valid
    }
}

#[derive(Clone, Debug)]
struct Matching {
    edges: Vec<(Node, Node)>,
    graph_nodes: Vec<Vec<Node>>,
}

impl Display for Matching {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{{")?;
        for (v1, v2) in &self.edges {
            let c1 = self.graph_nodes.iter().find(|c| c.contains(v1)).unwrap();
            let p1 = c1.iter().position(|v| v == v1).unwrap();
            let c2 = self.graph_nodes.iter().find(|c| c.contains(v2)).unwrap();
            let p2 = c2.iter().position(|v| v == v2).unwrap();
            write!(f, "(v{},u{}),", p1, p2)?;
        }
        write!(f, "}}")
    }
}

fn find_local_merge_with_matching<C: CreditInvariant>(
    graph: &Graph,
    graph_components: Vec<&Component>,
    credit_inv: C,
) -> bool {
    let sellable = edges_of_type(graph, EdgeType::Sellable);
    let buyable = edges_of_type(graph, EdgeType::Buyable);

    //dbg!(&buyable);
    //dbg!(&sellable);

    let total_component_credits = graph_components.iter().map(|c| credit_inv.credits(c)).sum();
    let new_component_credit = if graph_components
        .iter()
        .any(|c| matches!(c, Component::Complex(_)))
    {
        credit_inv.complex()
    } else {
        credit_inv.large()
    };

    let result = find_feasible_configuration(
        graph,
        buyable.into_iter().powerset().filter(|p| p.len() >= 2),
        sellable.into_iter().powerset(),
        new_component_credit,
        total_component_credits,
    );

    result
}

pub fn find_feasible_configuration<'a, B, S>(
    graph: &Graph,
    buy_iter: B,
    sell_iter: S,
    new_component_credit: Credit,
    total_component_credits: Credit,
) -> bool
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

            if total_plus_sell - buy_credits < new_component_credit {
                continue;
            }

            // Do the most expensive check last!
            if no_bridges_and_connected(&check_graph) {
                return true;
            }
        }
    }
    false
}
