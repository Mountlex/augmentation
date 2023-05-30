use itertools::Itertools;
use std::fmt::Debug;

use crate::proof_tree::ProofNode;

use rayon::prelude::{IntoParallelIterator, ParallelIterator};

pub trait InstanceTrait: Clone + Send + Sync {
    type StackElement: Sized + Clone + Debug + Send + Sync;
    type Payload: Sized + Clone + Debug + Send + Sync;

    fn item_msg(&self, item: &Self::StackElement, enum_msg: &str) -> String;

    fn push(&mut self, item: Self::StackElement);
    fn pop(&mut self);
}

pub trait OptEnumeratorTrait: Clone + Send + Sync {
    type Inst: InstanceTrait;

    fn msg(&self) -> &str;

    fn try_iter(
        &self,
        instance: &mut Self::Inst,
    ) -> Option<(
        Box<dyn Iterator<Item = <Self::Inst as InstanceTrait>::StackElement>>,
        String,
    )>;
}

pub trait EnumeratorTrait: Clone + Send + Sync {
    type Inst: InstanceTrait;

    fn msg(&self) -> &str;

    fn get_iter(
        &self,
        instance: &Self::Inst,
    ) -> Box<dyn Iterator<Item = <Self::Inst as InstanceTrait>::StackElement>>;
}

pub trait TacticTrait: Clone + Send + Sync {
    type Inst: InstanceTrait;

    fn prove(&self, stack: &mut Self::Inst) -> ProofNode<<Self::Inst as InstanceTrait>::Payload>;
}

pub trait MapperTrait: Clone + Send + Sync {
    type Inst: InstanceTrait;
    fn stack_element(&self, stack: &Self::Inst) -> <Self::Inst as InstanceTrait>::StackElement;
}

#[derive(Debug, Clone)]
pub enum Expression<E, OE, T, M> {
    Quantor(Quantor<E, OE, T, M>),
    Tactic(T),
    Or(Box<Expression<E, OE, T, M>>, Box<Expression<E, OE, T, M>>),
    And(Box<Expression<E, OE, T, M>>, Box<Expression<E, OE, T, M>>),
    Map(M, Box<Expression<E, OE, T, M>>),
}

impl<I, E, OE, T, M> Expression<E, OE, T, M>
where
    I: InstanceTrait,
    E: EnumeratorTrait<Inst = I>,
    OE: OptEnumeratorTrait<Inst = I>,
    T: TacticTrait<Inst = I>,
    M: MapperTrait<Inst = I>,
{
    pub fn prove(&self, stack: &mut I) -> ProofNode<I::Payload> {
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
            Expression::And(f1, f2) => {
                let mut proof1 = f1.prove(stack);
                proof1.eval();
                if !proof1.success() {
                    proof1
                } else {
                    let proof2 = f2.prove(stack);
                    ProofNode::new_and(proof1, proof2)
                }
            }
            Expression::Map(mapper, expression) => {
                let element = mapper.stack_element(stack);
                stack.push(element);
                let result = expression.prove(stack);
                stack.pop();
                result
            }
        }
    }
}

#[derive(Debug, Clone)]
pub enum Quantor<E, OE, T, M> {
    All(E, Box<Expression<E, OE, T, M>>, bool),
    AllOpt(
        OE,
        Box<Expression<E, OE, T, M>>,
        Box<Expression<E, OE, T, M>>,
        bool,
    ),
    AllOptPar(
        OE,
        Box<Expression<E, OE, T, M>>,
        Box<Expression<E, OE, T, M>>,
        bool,
    ),
    Any(E, Box<Expression<E, OE, T, M>>),
}

impl<
        I: InstanceTrait,
        E: EnumeratorTrait<Inst = I>,
        OE: OptEnumeratorTrait<Inst = I>,
        T: TacticTrait<Inst = I>,
        M: MapperTrait<Inst = I>,
    > Quantor<E, OE, T, M>
{
    fn formula(&self) -> &Box<Expression<E, OE, T, M>> {
        match self {
            Quantor::All(_, t, _) => t,
            Quantor::AllOpt(_, t, _, _) => t,
            Quantor::AllOptPar(_, t, _, _) => t,
            Quantor::Any(_, t) => t,
        }
    }

    fn prove(&self, stack: &mut I) -> ProofNode<I::Payload> {
        let mut enum_msg = String::new();
        let (case_iterator, otherwise) = match self {
            Quantor::All(e, _, _sc) => (Some(e.get_iter(stack)), None),
            Quantor::Any(e, _) => (Some(e.get_iter(stack)), None),
            Quantor::AllOpt(e, _, otherwise, _) | Quantor::AllOptPar(e, _, otherwise, _) => {
                if let Some((cases, msg)) = e.try_iter(stack) {
                    enum_msg = msg;
                    (Some(cases), Some(otherwise))
                } else {
                    (None, Some(otherwise))
                }
                //(None, Some(otherwise))
            }
        };

        if let Some(case_iterator) = case_iterator {
            let mut proof = match self {
                Quantor::All(e, _, _) => ProofNode::new_all(e.msg().to_string()),
                Quantor::AllOpt(e, _, _, _) => ProofNode::new_all(e.msg().to_string()),
                Quantor::AllOptPar(e, _, _, _) => ProofNode::new_all(e.msg().to_string()),
                Quantor::Any(e, _) => ProofNode::new_any(e.msg().to_string()),
            };

            //if false {
            if let Quantor::AllOptPar(_, _, _, _) = self {
                let cases = case_iterator.collect_vec();
                let nodes: Vec<_> = cases
                    .into_par_iter()
                    .map(|case| {
                        let item_msg = stack.item_msg(&case, &enum_msg);
                        let mut stack = stack.clone();
                        stack.push(case);
                        let mut proof_item = self.formula().prove(&mut stack);
                        proof_item = ProofNode::new_info(item_msg, proof_item);
                        let _outcome = proof_item.eval();

                        // if let Quantor::AllOpt(OptEnumerator::PathNode, _, _, _) = self {
                        //     proof_item.add_payload(stack.get_profile(outcome.success()));
                        // }

                        proof_item
                    })
                    .collect();
                for node in nodes {
                    proof.add_child(node);
                }
            } else {
                for case in case_iterator {
                    let item_msg = stack.item_msg(&case, &enum_msg);
                    stack.push(case);
                    let mut proof_item = self.formula().prove(stack);
                    proof_item = ProofNode::new_info(item_msg, proof_item);
                    let outcome = proof_item.eval();

                    // if let Quantor::AllOpt(OptEnumerator::PathNode, _, _, _) = self {
                    //     proof_item.add_payload(stack.get_profile(outcome.success()));
                    // }

                    proof.add_child(proof_item);
                    let res = outcome.success();
                    stack.pop();

                    let should_break = match self {
                        Quantor::AllOptPar(_, _, _, _sc) => {
                            panic!("We should not be in this case.")
                        }
                        Quantor::AllOpt(_, _, _, sc) => !res && *sc,
                        Quantor::All(_, _, sc) => !res && *sc,
                        Quantor::Any(_, _) => res,
                    };

                    if should_break {
                        break;
                    }
                }
            }

            proof.eval_and_prune();

            proof
        } else {
            otherwise.unwrap().prove(stack)
        }
    }
}

pub fn map<E, OE, T, M>(mapper: M, expr: Expression<E, OE, T, M>) -> Expression<E, OE, T, M> {
    Expression::Map(mapper, Box::new(expr))
}

pub fn and<E, OE, T, M>(
    expr1: Expression<E, OE, T, M>,
    expr2: Expression<E, OE, T, M>,
) -> Expression<E, OE, T, M> {
    Expression::And(Box::new(expr1), Box::new(expr2))
}

pub fn or<E, OE, T, M>(
    expr1: Expression<E, OE, T, M>,
    expr2: Expression<E, OE, T, M>,
) -> Expression<E, OE, T, M> {
    Expression::Or(Box::new(expr1), Box::new(expr2))
}

pub fn or3<E, OE, T, M>(
    expr1: Expression<E, OE, T, M>,
    expr2: Expression<E, OE, T, M>,
    expr3: Expression<E, OE, T, M>,
) -> Expression<E, OE, T, M> {
    or(expr1, or(expr2, expr3))
}

pub fn or4<E, OE, T, M>(
    expr1: Expression<E, OE, T, M>,
    expr2: Expression<E, OE, T, M>,
    expr3: Expression<E, OE, T, M>,
    expr4: Expression<E, OE, T, M>,
) -> Expression<E, OE, T, M> {
    or(expr1, or3(expr2, expr3, expr4))
}

pub fn or5<E, OE, T, M>(
    expr1: Expression<E, OE, T, M>,
    expr2: Expression<E, OE, T, M>,
    expr3: Expression<E, OE, T, M>,
    expr4: Expression<E, OE, T, M>,
    expr5: Expression<E, OE, T, M>,
) -> Expression<E, OE, T, M> {
    or(expr1, or4(expr2, expr3, expr4, expr5))
}

#[allow(dead_code)]
pub fn or6<E, OE, T, M>(
    expr1: Expression<E, OE, T, M>,
    expr2: Expression<E, OE, T, M>,
    expr3: Expression<E, OE, T, M>,
    expr4: Expression<E, OE, T, M>,
    expr5: Expression<E, OE, T, M>,
    expr6: Expression<E, OE, T, M>,
) -> Expression<E, OE, T, M> {
    or(expr1, or5(expr2, expr3, expr4, expr5, expr6))
}

pub fn expr<E, OE, T, M>(tactic: T) -> Expression<E, OE, T, M> {
    Expression::Tactic(tactic)
}

pub fn all_sc<E, OE, T, M>(
    enumerator: E,
    expr: Expression<E, OE, T, M>,
) -> Expression<E, OE, T, M> {
    Expression::Quantor(Quantor::All(enumerator, Box::new(expr), true))
}

// pub fn all(enumerator: Enumerator, expr: Expression<E,OE,T,M>, sc: bool) -> Expression<E,OE,T,M> {
//     Expression::Quantor(Quantor::All(enumerator, Box::new(expr), sc))
// }

pub fn all_opt<E, OE, T, M>(
    enumerator: OE,
    expr: Expression<E, OE, T, M>,
    otherwise: Expression<E, OE, T, M>,
    sc: bool,
) -> Expression<E, OE, T, M> {
    Expression::Quantor(Quantor::AllOpt(
        enumerator,
        Box::new(expr),
        Box::new(otherwise),
        sc,
    ))
}

pub fn all_opt_par<E, OE, T, M>(
    enumerator: OE,
    expr: Expression<E, OE, T, M>,
    otherwise: Expression<E, OE, T, M>,
    sc: bool,
) -> Expression<E, OE, T, M> {
    Expression::Quantor(Quantor::AllOptPar(
        enumerator,
        Box::new(expr),
        Box::new(otherwise),
        sc,
    ))
}

pub fn any<E, OE, T, M>(enumerator: E, expr: Expression<E, OE, T, M>) -> Expression<E, OE, T, M> {
    Expression::Quantor(Quantor::Any(enumerator, Box::new(expr)))
}
