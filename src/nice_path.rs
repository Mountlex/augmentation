use itertools::Itertools;
use num_rational::Rational64;

use crate::{
    comps::{merge_graphs, Component, CreditInvariant, EdgeType, Graph},
    edges_of_type,
    local_merge::{find_feasible_merge, FeasibleMerge, MergeResult},
};

#[derive(Clone)]
enum Node {
    NicePair(Component),
    Any(Component),
}

impl Node {
    fn get_graph(&self) -> Graph {
        match self {
            Node::NicePair(_) => Graph::from_edges(vec![(0, 0, EdgeType::Fixed)]),
            Node::Any(comp) => comp.graph().clone(),
        }
    }

    fn credit<C: CreditInvariant>(&self, credit_inv: C) -> Rational64 {
        match self {
            Node::NicePair(c) => credit_inv.credits(c) + Rational64::from_integer(1),
            Node::Any(c) => credit_inv.credits(c),
        }
    }
}

struct NicePath {
    first: Node,
    //fill: Vec<Node>,
    prelast: Node,
    last: Node,
}

fn sum_of_credits<C: CreditInvariant>(nodes: Vec<&Node>, credit_inv: C) -> Rational64 {
    nodes
        .into_iter()
        .map(|n| n.credit(credit_inv.clone()))
        .sum()
}

pub fn prove_nice_path_progress<C: CreditInvariant>(comps: Vec<Component>, credit_inv: C) {
    for f in &comps {
        let nf = Node::Any(f.clone());

        for p in &comps {
            let np = if let Component::Cycle(_) = p {
                Node::NicePair(p.clone())
            } else {
                Node::Any(p.clone())
            };
            for l in &comps {
                let nl = if let Component::Cycle(_) = l {
                    Node::NicePair(l.clone())
                } else {
                    Node::Any(l.clone())
                };

                let path = NicePath {
                    first: nf.clone(),
                    prelast: np.clone(),
                    last: nl.clone(),
                };

                if prove_nice_path(path, credit_inv.clone()) {
                    println!("✔️ Nice path progress for {} -- {} -- {}", f, p, l);
                } else {
                    println!("❌ Nice path progress for {} -- {} -- {}", f, p, l);
                }
            }
        }
    }
}

fn prove_nice_path<C: CreditInvariant>(path: NicePath, credit_inv: C) -> bool {
    let first_graph = path.first.get_graph();
    let prelast_graph = path.prelast.get_graph();
    let last_graph = path.last.get_graph();
    let (graph, nodes) = merge_graphs(vec![first_graph, prelast_graph, last_graph]);
    let [first_graph, prelast_graph, last_graph] = <[Graph; 3]>::try_from(nodes).ok().unwrap();

    for (f_out, f_in, p_out, p_in, l_out, l_in) in itertools::iproduct!(
        first_graph.nodes(),
        first_graph.nodes(),
        prelast_graph.nodes(),
        prelast_graph.nodes(),
        last_graph.nodes(),
        last_graph.nodes()
    ) {
        let cycle = vec![(f_out, l_in), (l_out, p_in), (p_out, f_in)];
        let sellable = edges_of_type(&graph, EdgeType::Sellable);
        let total_component_credits = sum_of_credits(
            vec![&path.first, &path.prelast, &path.last],
            credit_inv.clone(),
        );

        let mut graph_copy = graph.clone();
        for (v1, v2) in &cycle {
            graph_copy.add_edge(*v1, *v2, EdgeType::Buyable);
        }

        let result = find_feasible_merge(
            &graph_copy,
            vec![cycle].into_iter(),
            sellable.into_iter().powerset(),
            credit_inv.large(),
            credit_inv.clone(),
            todo!(),
        );
        if let MergeResult::FeasibleLarge(_) | MergeResult::FeasibleComplex(_) = result {
            //println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
            return false;
        }
    }

    true
}
