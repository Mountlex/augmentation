use std::fmt::Display;

use itertools::Itertools;

use crate::{comps::Component, proof_tree::ProofNode, types::Edge, Node};

use super::{AbstractEdge, Pidx};

#[derive(Clone)]
struct InstPart {
    path_nodes: Vec<PathNode>,
    nice_pairs: Vec<(Node, Node)>,
    edges: Vec<Edge>,
    out_edges: Vec<AbstractEdge>,
    rem_edges: Vec<AbstractEdge>,
    non_rem_edges: Vec<AbstractEdge>,
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
        }
    }
}

impl Display for InstPart {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        todo!()
    }
}

#[derive(Clone)]
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

#[derive(Clone)]
struct Instance {
    stack: Vec<StackElement>,
}

impl Instance {
    fn push(&mut self, ele: StackElement) {
        self.stack.push(ele);
    }

    fn pop(&mut self) {
        self.stack.pop();
    }

    fn inst_parts<'a>(&'a self)  -> impl Iterator<Item = &'a InstPart> {
        self.stack.iter().flat_map(|ele| ele.as_inst_part())
    }

    fn path_nodes<'a>(&'a self) -> impl Iterator<Item = &'a PathNode> {
        self.inst_parts().flat_map(|part| part.path_nodes.iter())
    }

    fn nice_pairs<'a>(&'a self) -> impl Iterator<Item = &'a (Node, Node)> {
        self.inst_parts().flat_map(|part| part.nice_pairs.iter())
    }

    fn out_edges<'a>(&'a self) -> impl Iterator<Item = &'a AbstractEdge> {
        self.inst_parts().flat_map(|part| part.out_edges.iter())
    }

    fn rem_edges<'a>(&'a self) -> Vec<&'a AbstractEdge> {
        let mut rem_edges: Vec<&'a AbstractEdge> = vec![];
        for part in self.inst_parts() {
            let non_sources = part.non_rem_edges.iter().map(|e| e.source()).collect_vec();
            if non_sources.len() > 0 {
                rem_edges.drain_filter(|e| non_sources.contains(&e.source));
            }
            rem_edges.append(&mut part.rem_edges.iter().collect_vec());
        }
        rem_edges
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

// #[derive(Clone)]
// enum PathNode {
//     Abstract(AbstractNode),
//     Concrete(ConcreteNode),
// }

#[derive(Clone)]
struct PathNode {
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
    fn get_iter(&self, stack: &Instance) -> impl Iterator<Item = StackElement> {
        std::iter::empty()
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
