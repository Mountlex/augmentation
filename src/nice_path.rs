use itertools::Itertools;
use num_rational::Rational64;

use crate::{
    comps::{Component, CreditInvariant, EdgeType, Graph},
    edges_of_type, enumerate_and_check, merge_graphs, relabel_nodes,
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
            Node::Any(comp) => comp.graph(),
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
            let np = if let Component::Simple(_) = p {
                Node::NicePair(p.clone())
            } else {
                Node::Any(p.clone())
            };
            for l in &comps {
                let nl = if let Component::Simple(_) = l {
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
    let mut first_graph = path.first.get_graph();
    let mut prelast_graph = path.prelast.get_graph();
    let mut last_graph = path.last.get_graph();
    relabel_nodes(vec![&mut first_graph, &mut prelast_graph, &mut last_graph]);
    let graph = merge_graphs(vec![&first_graph, &prelast_graph, &last_graph]);

    let f_nodes: Vec<u32> = first_graph.nodes().collect();
    let p_nodes: Vec<u32> = prelast_graph.nodes().collect();
    let l_nodes: Vec<u32> = last_graph.nodes().collect();

    for (f_out, f_in, p_out, p_in, l_out, l_in) in itertools::iproduct!(
        f_nodes.clone(),
        f_nodes,
        p_nodes.clone(),
        p_nodes,
        l_nodes.clone(),
        l_nodes
    ) {
        let cycle = vec![
            (f_out, l_in, EdgeType::Zero),
            (l_out, p_in, EdgeType::Zero),
            (p_out, f_in, EdgeType::Zero),
        ];
        let sellable = edges_of_type(&graph, EdgeType::One);
        let previous_credits = sum_of_credits(
            vec![&path.first, &path.prelast, &path.last],
            credit_inv.clone(),
        );

        let result = enumerate_and_check(
            &graph,
            vec![cycle].into_iter(),
            sellable.into_iter().powerset(),
            credit_inv.clone(),
            previous_credits,
        );
        if !result {
            //println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
            return false;
        }
    }

    true
}
