use itertools::Itertools;
use num_rational::Rational64;
use petgraph::{
    data::Build,
    dot::{Config, Dot},
};

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
            Node::NicePair(_) => {
                let mut g = Graph::new();
                g.add_node(0);
                g
            }
            Node::Any(comp) => comp.graph(),
        }
    }

    fn as_comp<'a>(&'a self) -> &'a Component {
        match self {
            Node::NicePair(c) => c,
            Node::Any(c) => c,
        }
    }
}

struct NicePath {
    first: Node,
    //fill: Vec<Node>,
    prelast: Node,
    last: Node,
}

fn all_tuples<T: Eq + Copy>(list: Vec<T>) -> Vec<(T, T)> {
    if list[0] != list[1] {
        vec![(list[0], list[1]), (list[1], list[0])]
    } else {
        vec![(list[0], list[1])]
    }
}

fn sum_of_credits<C: CreditInvariant>(nodes: Vec<&Node>, credit_inv: C) -> Rational64 {
    nodes
        .into_iter()
        .map(|n| credit_inv.credits(n.as_comp()))
        .sum()
}

pub fn prove_cycle_case<C: CreditInvariant>(comps: Vec<Component>, credit_inv: C) {
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

                prove_nice_path(path, credit_inv.clone());
                println!("Checked nice path {} -- {} -- {}!", f, p, l);
            }
        }
    }
}

fn prove_nice_path<C: CreditInvariant>(path: NicePath, credit_inv: C) {
    let mut first_graph = path.first.get_graph();
    let mut prelast_graph = path.prelast.get_graph();
    let mut last_graph = path.last.get_graph();
    relabel_nodes(vec![&mut first_graph, &mut prelast_graph, &mut last_graph]);
    let graph = merge_graphs(vec![&first_graph, &prelast_graph, &last_graph]);

    let f_nodes: Vec<u32> = first_graph.nodes().collect();
    let p_nodes: Vec<u32> = prelast_graph.nodes().collect();
    let l_nodes: Vec<u32> = last_graph.nodes().collect();

    for f_perm in f_nodes.iter().combinations_with_replacement(2) {
        for (&f_out, &f_in) in all_tuples(f_perm) {
            for p_perm in p_nodes.iter().combinations_with_replacement(2) {
                for (&p_out, &p_in) in all_tuples(p_perm) {
                    for l_perm in l_nodes.iter().combinations_with_replacement(2) {
                        for (&l_out, &l_in) in all_tuples(l_perm) {
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

                            let t = vec![cycle];
                            let result = enumerate_and_check(
                                &graph,
                                t.into_iter(),
                                sellable.into_iter().powerset(),
                                credit_inv.clone(),
                                previous_credits,
                            );
                            if !result {
                                println!("{:?}", Dot::with_config(&graph, &[Config::EdgeNoLabel]));
                                panic!("Graph cannot be shortcutted!");
                            }
                        }
                    }
                }
            }
        }
    }
}
