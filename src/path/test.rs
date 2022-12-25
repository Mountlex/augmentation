use std::fmt::Display;

use itertools::Itertools;

use crate::{
    comps::Component, proof_tree::ProofNode, types::Edge, util::relabels_nodes_sequentially,
    CreditInv, Node,
};

use super::{proof::PathNode, AbstractEdge, NicePairConfig, Pidx};

#[derive(Clone, Debug)]
struct InstPart {
    path_nodes: Vec<PathComp>,
    nice_pairs: Vec<(Node, Node)>,
    edges: Vec<Edge>,
    out_edges: Vec<Node>,
    rem_edges: Vec<MatchingEdge>,
    non_rem_edges: Vec<MatchingEdge>,
    connected_nodes: Vec<Node>,
}

#[derive(Clone, Debug)]
struct MatchingEdge {
    source: Node,
    source_idx: Pidx,
    matching: bool,
}

impl InstPart {
    fn empty() -> InstPart {
        InstPart {
            path_nodes: vec![],
            nice_pairs: vec![],
            edges: vec![],
            out_edges: vec![],
            rem_edges: vec![],
            non_rem_edges: vec![],
            connected_nodes: vec![],
        }
    }

    fn new_path_comp(path_comp: PathComp) -> InstPart {
        InstPart {
            path_nodes: vec![path_comp],
            nice_pairs: vec![],
            edges: vec![],
            out_edges: vec![],
            rem_edges: vec![],
            non_rem_edges: vec![],
            connected_nodes: vec![],
        }
    }
}

impl Display for InstPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

#[derive(Clone, Debug)]
enum StackElement {
    Inst(InstPart),
    PseudoCycle,
}

impl StackElement {
    fn as_inst_part(&self) -> Option<&InstPart> {
        match self {
            StackElement::Inst(inst) => Some(inst),
            StackElement::PseudoCycle => None,
        }
    }
}

impl Display for StackElement {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StackElement::Inst(part) => write!(f, "{}", part),
            StackElement::PseudoCycle => todo!(),
        }
    }
}

#[derive(Clone, Debug)]
struct InstanceContext {
    inv: CreditInv,
    comps: Vec<PathNode>,
}

#[derive(Clone, Debug)]
struct Instance {
    stack: Vec<StackElement>,
    context: InstanceContext,
}

impl Instance {
    fn push(&mut self, ele: StackElement) {
        self.stack.push(ele);
    }

    fn pop(&mut self) {
        self.stack.pop();
    }

    fn inst_parts<'a>(&'a self) -> impl Iterator<Item = &'a InstPart> {
        self.stack.iter().flat_map(|ele| ele.as_inst_part())
    }

    fn path_nodes<'a>(&'a self) -> impl Iterator<Item = &'a PathComp> {
        self.inst_parts().flat_map(|part| part.path_nodes.iter())
    }

    fn nice_pairs<'a>(&'a self) -> impl Iterator<Item = &'a (Node, Node)> {
        self.inst_parts().flat_map(|part| part.nice_pairs.iter())
    }

    fn out_edges<'a>(&'a self) -> impl Iterator<Item = &'a Node> {
        self.inst_parts().flat_map(|part| part.out_edges.iter())
    }

    fn connected_nodes<'a>(&'a self) -> impl Iterator<Item = &'a Node> {
        self.inst_parts()
            .flat_map(|part| part.connected_nodes.iter())
    }

    fn rem_edges<'a>(&'a self) -> Vec<&'a MatchingEdge> {
        let mut rem_edges: Vec<&'a MatchingEdge> = vec![];
        for part in self.inst_parts() {
            let non_sources = &part
                .non_rem_edges
                .iter()
                .map(|edge| edge.source)
                .collect_vec();
            if non_sources.len() > 0 {
                rem_edges.drain_filter(|edge| non_sources.contains(&edge.source));
            }
            rem_edges.append(&mut part.rem_edges.iter().collect_vec());
        }
        rem_edges
    }

    fn npc<'a>(&'a self) -> NicePairConfig {
        let tuples = self
            .inst_parts()
            .flat_map(|part| part.nice_pairs.iter())
            .unique()
            .cloned()
            .collect_vec();
        NicePairConfig { nice_pairs: tuples }
    }

    fn implied_edges<'a>(&'a self) -> impl Iterator<Item = &'a Edge> {
        self.inst_parts().flat_map(|part| part.edges.iter())
    }

    fn all_edges<'a>(&'a self) -> Vec<Edge> {
        let mut implied_edges = self.implied_edges().cloned().collect_vec();
        let nodes = self.path_nodes().collect_vec();
        for w in nodes.windows(2) {
            implied_edges.push(Edge::new(
                w[0].in_node.unwrap(),
                w[0].path_idx,
                w[1].out_node.unwrap(),
                w[1].path_idx,
            ));
        }

        implied_edges
    }
}

// #[derive(Clone,Debug)]
// enum PathNode {
//     Abstract(AbstractNode),
//     Concrete(ConcreteNode),
// }

#[derive(Clone, Debug)]
struct PathComp {
    comp: Component,
    in_node: Option<Node>,
    out_node: Option<Node>,
    used: bool,
    path_idx: Pidx,
}

enum Quantor {
    All(Enumerator, Box<Expression>),
    Any(Enumerator, Box<Expression>),
}

impl Quantor {
    fn enumerator(&self) -> &Enumerator {
        match self {
            Quantor::All(e, _) => e,
            Quantor::Any(e, _) => e,
        }
    }

    fn formula(&self) -> &Box<Expression> {
        match self {
            Quantor::All(_, t) => t,
            Quantor::Any(_, t) => t,
        }
    }

    fn prove(&self, stack: &mut Instance) -> ProofNode {
        let mut proof = match self {
            Quantor::All(_, _) => ProofNode::new_all(format!("TODO")),
            Quantor::Any(_, _) => ProofNode::new_any(format!("TODO")),
        };

        let iter = self.enumerator().get_iter(&stack);

        for instance in iter {
            let item_msg = format!("{}", instance);
            stack.push(instance);
            let mut proof_item = self.formula().prove(stack);
            proof_item = ProofNode::new_info(item_msg, proof_item);
            let outcome = proof_item.eval();
            proof.add_child(proof_item);
            let res = outcome.success();
            stack.pop();

            let should_break = match self {
                Quantor::All(_, _) => !res,
                Quantor::Any(_, _) => res,
            };

            if should_break {
                break;
            }
        }

        proof
    }
}

enum Enumerator {
    Edges,
    PathNodes, // includes enumeration of in and out
    NicePairs,
    PseudoCycle,
    Rearrangments,
}

impl Enumerator {
    fn get_iter(&self, stack: &Instance) -> Box<dyn Iterator<Item = StackElement>> {
        todo!()
    }
}

// TODO READ
fn path_node_enumerator(instance: &Instance) -> Box<dyn Iterator<Item = StackElement> + '_> {
    let path_comps = instance.path_nodes().collect_vec();
    let old_path_len = path_comps.len();
    let all_edges = instance.all_edges();
    let rem_edges = instance.rem_edges();

    let iter = instance.context.comps.iter().flat_map(move |node| {
        let comp = node.get_comp().clone();
        let num_used_labels = path_comps
            .iter()
            .map(|c| c.comp.num_labels())
            .sum::<usize>() as u32;
        let mut new_comps = vec![comp];
        relabels_nodes_sequentially(&mut new_comps, num_used_labels);
        let comp = new_comps.remove(0);
        let node = match node {
            PathNode::Used(_) => PathNode::Used(comp.clone()),
            PathNode::Unused(_) => PathNode::Unused(comp.clone()),
        };

        let rem_edges = rem_edges.clone();
        let node_idx = path_comps.last().unwrap().path_idx.prec();

        let out_nodes = if let Some(fixed) = comp.fixed_node() {
            vec![fixed] // we assume here that if comp has a fixed node it was not used for any matching hit node.
        } else {
            let succ = node_idx.succ().unwrap();
            let matching_endpoints_at_new = all_edges
                .iter()
                .filter(|&edge| edge.between_path_nodes(succ, node_idx))
                .into_iter()
                .flat_map(|e| e.endpoint_at(node_idx))
                .collect_vec();

            comp.matching_nodes()
                .into_iter()
                .filter(|&n| !matching_endpoints_at_new.contains(n))
                .cloned()
                .collect_vec()
        };

        let in_nodes = if !node_idx.is_last() {
            comp.matching_nodes().to_vec()
        } else {
            if let Some(fixed) = comp.fixed_node() {
                vec![fixed]
            } else {
                comp.matching_nodes().to_vec()
            }
        };

        let comp_filter = comp.clone();
        let comp_map = comp.clone();
        let node_filter = node.clone();
        let node_map = node.clone();

        let iter: Box<dyn Iterator<Item = PathComp>> =
            Box::new(in_nodes.into_iter().flat_map(move |in_node| {
                let comp_filter = comp_filter.clone();
                let comp_map = comp_map.clone();
                let node_filter = node_filter.clone();
                let node_map = node_map.clone();

                let iter: Box<dyn Iterator<Item = PathComp>> = Box::new(
                    // case where we not consider the last node --> we need an out node
                    out_nodes
                        .clone()
                        .into_iter()
                        .filter(move |out_node| {
                            valid_in_out(
                                &comp_filter,
                                in_node,
                                *out_node,
                                node_idx.is_prelast(),
                                node_filter.is_used(),
                            )
                        })
                        .map(move |out_node| PathComp {
                            comp: comp_map.clone(),
                            in_node: Some(in_node),
                            out_node: Some(out_node),
                            used: node_map.is_used(),
                            path_idx: node_idx,
                        }),
                );
                iter
            }));

        let iter: Box<dyn Iterator<Item = InstPart>> =
            Box::new(iter.into_iter().flat_map(move |path_comp| {
                let comp = comp.clone();

                let rem_edges_copy = rem_edges.iter().cloned().cloned().collect_vec();
                rem_edges_copy
                    .into_iter()
                    .powerset()
                    .flat_map(move |hits_node| {
                        let comp = comp.clone();

                        // hits_node is the set of edges which now should hit node_idx
                        let mut iter: Box<dyn Iterator<Item = InstPart>> =
                            Box::new(vec![InstPart::new_path_comp(path_comp.clone())].into_iter());
                        for i in 0..old_path_len {
                            let source_idx = Pidx::from(i);
                            let comp = comp.clone();

                            // all matching edges between source_idx and node_idx
                            let matching_edges = hits_node
                                .clone()
                                .into_iter()
                                .filter(|e| e.source_idx == source_idx)
                                .collect_vec();

                            let non_rem_edges = hits_node.clone();

                            iter = Box::new(iter.into_iter().flat_map(move |inst_part| {
                                let matching_edges = matching_edges.clone();
                                let non_rem_edges = non_rem_edges.clone();

                                let tmp: Box<dyn Iterator<Item = InstPart>> = Box::new(
                                    comp.matching_permutations(matching_edges.len())
                                        .into_iter()
                                        .filter(move |matched| {
                                            if source_idx.prec() == node_idx {
                                                if let Some(out) = path_comp.out_node {
                                                    out.is_comp()
                                                        || matched
                                                            .iter()
                                                            .all(|matched| *matched != out)
                                                } else {
                                                    true
                                                }
                                            } else {
                                                true
                                            }
                                        })
                                        .map(move |matched| {
                                            let mut edges = matched
                                                .into_iter()
                                                .zip(matching_edges.iter())
                                                .map(|(u, v)| {
                                                    Edge::new(v.source, source_idx, u, node_idx)
                                                })
                                                .collect_vec();

                                            let mut non_rem_edges = non_rem_edges.clone();

                                            let mut inst_part_copy = inst_part.clone();
                                            inst_part_copy.edges.append(&mut edges);
                                            inst_part_copy.non_rem_edges.append(&mut non_rem_edges);
                                            inst_part_copy
                                        }),
                                );

                                tmp
                            }))
                        }

                        iter
                    })
            }));

        iter
    });

    Box::new(iter.into_iter().map(|ele| StackElement::Inst(ele)));
    todo!("READ")
}

fn nice_pairs_enumerator(instance: &Instance) -> Box<dyn Iterator<Item = StackElement>> {
    let all_edges = instance.all_edges();
    let rem_edges = instance.rem_edges();
    let out_edges = instance.out_edges().collect_vec();
    let npc = instance.npc();
    let connected_nodes = instance.connected_nodes().collect_vec();

    let nodes_with_edges = all_edges
        .iter()
        .flat_map(|e| e.to_vec())
        .chain(rem_edges.iter().map(|e| e.source))
        .chain(out_edges.iter().cloned().cloned())
        .collect_vec();

    let mut cases: Box<dyn Iterator<Item = InstPart>> =
        Box::new(vec![InstPart::empty()].into_iter());
    let path_comps = instance.path_nodes().collect_vec();

    for path_comp in path_comps {
        let updated_nodes_with_edges = path_comp
            .comp
            .matching_nodes()
            .into_iter()
            .filter(|n| nodes_with_edges.contains(n))
            .cloned()
            .collect_vec();
        let path_comp_nodes = path_comp.comp.matching_nodes();
        let comp_conn_nodes = connected_nodes
            .iter()
            .filter(|n| path_comp_nodes.contains(&n))
            .cloned()
            .cloned()
            .collect_vec();

        let npc = npc.clone();
        
        cases = Box::new(cases.into_iter().flat_map(move |inst_part| {
            let npc = npc.clone();
            let updated_nodes_with_edges = updated_nodes_with_edges.clone();

            let iter: Box<dyn Iterator<Item = InstPart>> =
                if comp_conn_nodes != updated_nodes_with_edges {
                    // node is already zoomed, just update nice pairs of new incident edges
                    let iter = comp_npcs(
                        &path_comp,
                        &updated_nodes_with_edges,
                        &npc,
                        &comp_conn_nodes,
                    )
                    .into_iter()
                    .map(move |mut npc| {
                        let mut inst_part_clone = inst_part.clone();

                        inst_part_clone.nice_pairs.append(&mut npc.nice_pairs);
                        inst_part_clone.nice_pairs.sort();
                        inst_part_clone.nice_pairs.dedup();

                        inst_part_clone
                            .connected_nodes
                            .append(&mut updated_nodes_with_edges.clone());
                        inst_part_clone.connected_nodes.sort();
                        inst_part_clone.connected_nodes.dedup();

                        inst_part_clone
                    });
                    Box::new(iter)
                } else {
                    Box::new(vec![inst_part].into_iter())
                };
            iter
        }));
    }

    Box::new(cases.into_iter().map(|ele| StackElement::Inst(ele)));
    todo!("READ")
}

fn comp_npcs(
    node: &PathComp,
    nodes: &[Node],
    consistent_npc: &NicePairConfig,
    consistent_nodes: &[Node],
) -> Vec<NicePairConfig> {
    let comp = &node.comp;

    match comp {
        Component::Large(_) => vec![NicePairConfig::empty()],
        Component::ComplexTree(_, black) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(&v2))
                .collect_vec(),
        }],
        Component::ComplexPath(_, black) => vec![NicePairConfig {
            nice_pairs: nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(v1, v2)| v1 != v2 || !black.contains(&v2))
                .collect_vec(),
        }],
        _ => {
            // cycle case
            nodes
                .iter()
                .cloned()
                .tuple_combinations::<(_, _)>()
                .filter(|(u, v)| !comp.is_adjacent(u, v))
                .powerset()
                .map(|config| NicePairConfig { nice_pairs: config })
                .map(|mut npc| {
                    // adjacent vertices are always nice pairs!
                    npc.nice_pairs.append(&mut comp.edges());
                    npc
                })
                .filter(|npc| npc.is_consistent_with(&consistent_npc, &consistent_nodes))
                .collect_vec()
        }
    }
}

fn valid_in_out(c: &Component, new_in: Node, new_out: Node, prelast: bool, used: bool) -> bool {
    if c.is_c3() || c.is_c4() || c.is_complex() || (c.is_c5() && prelast && used) {
        new_in != new_out
    } else {
        true
    }
}

enum Tactic {
    Or,
    LongerPath,
    CycleMerge,
    LocalMerge,
    Rearrangable,
}

impl Tactic {
    fn prove(&self, stack: &Instance) -> ProofNode {
        ProofNode::new_leaf("test".into(), false)
    }
}

enum Expression {
    Quantor(Quantor),
    Tactic(Tactic),
    Or(Box<Expression>, Box<Expression>),
}

impl Expression {
    fn prove(&self, stack: &mut Instance) -> ProofNode {
        match self {
            Expression::Quantor(q) => q.prove(stack),
            Expression::Tactic(t) => t.prove(stack),
            Expression::Or(f1, f2) => {
                let mut proof1 = f1.prove(stack);
                proof1.eval();
                if proof1.success() {
                    proof1
                } else {
                    let proof2 = f2.prove(stack);
                    ProofNode::new_or(proof1, proof2)
                }
            }
        }
    }
}

fn or(expr1: Expression, expr2: Expression) -> Expression {
    Expression::Or(Box::new(expr1), Box::new(expr2))
}

fn or3(expr1: Expression, expr2: Expression, expr3: Expression) -> Expression {
    or(expr1, or(expr2, expr3))
}

fn or4(expr1: Expression, expr2: Expression, expr3: Expression, expr4: Expression) -> Expression {
    or(expr1, or3(expr2, expr3, expr4))
}

fn tc(tactic: Tactic) -> Expression {
    Expression::Tactic(tactic)
}

fn all(enumerator: Enumerator, expr: Expression) -> Expression {
    Expression::Quantor(Quantor::All(enumerator, Box::new(expr)))
}

fn any(enumerator: Enumerator, expr: Expression) -> Expression {
    Expression::Quantor(Quantor::All(enumerator, Box::new(expr)))
}

fn test() {
    let proof = all(
        Enumerator::Edges,
        all(Enumerator::Edges, tc(Tactic::LongerPath)),
    );
}
