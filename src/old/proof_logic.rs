use std::marker::PhantomData;

use crate::proof_tree::DefaultProofNode;

pub trait EnumeratorTactic<I, O, C> {
    type Enumer<'a>: Enumerator<O, C>
    where
        Self: 'a,
        I: 'a;

    fn msg(&self, data_in: &I) -> String;
    fn get_enumerator<'a>(&'a self, data: &'a I) -> Self::Enumer<'a>;
    fn item_msg(&self, item: &O) -> String;
    fn precondition(&self, _data: &I, _context: &C) -> bool {
        true
    }
}

pub trait OptEnumeratorTactic<I, O, C> {
    type Enumer<'a>: OptEnumerator<O, C>
    where
        Self: 'a,
        I: 'a;

    fn msg(&self, data_in: &I) -> String;
    fn get_enumerator<'a>(&'a self, data: &'a I) -> Self::Enumer<'a>;
    fn item_msg(&self, item: &O) -> String;
    fn precondition(&self, _data: &I, _context: &C) -> bool {
        true
    }
}

pub trait Enumerator<O, C> {
    fn iter(&self, context: &C) -> Box<dyn Iterator<Item = O> + '_>;
}

pub trait OptEnumerator<O, C> {
    fn iter(&self, context: &C) -> Option<Box<dyn Iterator<Item = O> + '_>>;
}

pub trait Tactic<I, C> {
    fn precondition(&self, _data: &I, _context: &C) -> bool {
        true
    }

    fn action(&mut self, data: &I, context: &C) -> DefaultProofNode;
}

pub trait Statistics {
    fn print_stats(&self);
}

#[derive(Clone)]
pub struct If<I, A, F>
where
    F: Fn(&I) -> bool,
{
    tactic: A,
    cond: F,
    _phantom_data: PhantomData<I>,
}

impl<I, A, F> Statistics for If<I, A, F>
where
    A: Statistics,
    F: Fn(&I) -> bool,
{
    fn print_stats(&self) {
        self.tactic.print_stats()
    }
}

impl<I, A, F, C> Tactic<I, C> for If<I, A, F>
where
    A: Statistics + Tactic<I, C>,
    F: Fn(&I) -> bool,
{
    fn precondition(&self, data: &I, _context: &C) -> bool {
        (self.cond)(data)
    }

    fn action(&mut self, data: &I, context: &C) -> DefaultProofNode {
        self.tactic.action(data, context)
    }
}

#[allow(dead_code)]
pub fn ifcond<I, A, F>(cond: F, tactic: A) -> If<I, A, F>
where
    F: Fn(&I) -> bool,
{
    If {
        tactic,
        cond,
        _phantom_data: PhantomData,
    }
}

#[derive(Clone)]
pub struct And<I, A1, A2> {
    tactic1: A1,
    tactic2: A2,
    _phantom_data: PhantomData<I>,
}

impl<I, A1, A2> Statistics for And<I, A1, A2>
where
    A1: Statistics,
    A2: Statistics,
{
    fn print_stats(&self) {
        self.tactic1.print_stats();
        self.tactic2.print_stats();
    }
}

pub fn and<I, A1, A2>(tactic1: A1, tactic2: A2) -> And<I, A1, A2> {
    And {
        tactic1,
        tactic2,
        _phantom_data: PhantomData,
    }
}

impl<I, A1, A2, C> Tactic<I, C> for And<I, A1, A2>
where
    A1: Tactic<I, C>,
    A2: Tactic<I, C>,
{
    fn action(&mut self, data: &I, context: &C) -> DefaultProofNode {
        let mut proof1 = self.tactic1.action(data, context);
        let outcome = proof1.eval();
        if !outcome.success() {
            proof1
        } else {
            let proof2 = self.tactic2.action(data, context);
            DefaultProofNode::new_and(proof1, proof2)
        }
    }

    fn precondition(&self, data: &I, context: &C) -> bool {
        self.tactic1.precondition(data, context) && self.tactic2.precondition(data, context)
    }
}

#[derive(Clone)]
pub struct Or<I, A1, A2> {
    tactic1: A1,
    tactic2: A2,
    _phantom_data: PhantomData<I>,
}

impl<I, A1, A2> Statistics for Or<I, A1, A2>
where
    A1: Statistics,
    A2: Statistics,
{
    fn print_stats(&self) {
        self.tactic1.print_stats();
        self.tactic2.print_stats();
    }
}

pub fn or<I, A1, A2>(tactic1: A1, tactic2: A2) -> Or<I, A1, A2> {
    Or {
        tactic1,
        tactic2,
        _phantom_data: PhantomData,
    }
}

pub fn or3<I, A1, A2, A3>(tactic1: A1, tactic2: A2, tactic3: A3) -> Or<I, A1, Or<I, A2, A3>> {
    or(tactic1, or(tactic2, tactic3))
}

pub fn or4<I, A1, A2, A3, A4>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
) -> Or<I, A1, Or<I, A2, Or<I, A3, A4>>> {
    or3(tactic1, tactic2, or(tactic3, tactic4))
}

pub fn or5<I, A1, A2, A3, A4, A5>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, A5>>>> {
    or4(tactic1, tactic2, tactic3, or(tactic4, tactic5))
}

#[allow(dead_code)]
pub fn or6<I, A1, A2, A3, A4, A5, A6>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
    tactic6: A6,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, Or<I, A5, A6>>>>> {
    or5(tactic1, tactic2, tactic3, tactic4, or(tactic5, tactic6))
}

#[allow(dead_code)]
pub fn or7<I, A1, A2, A3, A4, A5, A6, A7>(
    tactic1: A1,
    tactic2: A2,
    tactic3: A3,
    tactic4: A4,
    tactic5: A5,
    tactic6: A6,
    tactic7: A7,
) -> Or<I, A1, Or<I, A2, Or<I, A3, Or<I, A4, Or<I, A5, Or<I, A6, A7>>>>>> {
    or6(
        tactic1,
        tactic2,
        tactic3,
        tactic4,
        tactic5,
        or(tactic6, tactic7),
    )
}

impl<I, A1, A2, C> Tactic<I, C> for Or<I, A1, A2>
where
    A1: Tactic<I, C>,
    A2: Tactic<I, C>,
{
    fn action(&mut self, data: &I, context: &C) -> DefaultProofNode {
        if self.tactic1.precondition(data, context) {
            let mut proof1 = self.tactic1.action(data, context);
            let outcome = proof1.eval();
            if outcome.success() || !self.tactic2.precondition(data, context) {
                proof1
            } else {
                let proof2 = self.tactic2.action(data, context);
                DefaultProofNode::new_or(proof1, proof2)
            }
        } else {
            self.tactic2.action(data, context)
        }
    }

    fn precondition(&self, data: &I, context: &C) -> bool {
        self.tactic1.precondition(data, context) || self.tactic2.precondition(data, context)
    }
}

#[derive(Clone)]
pub struct AllOpt<O, E, T, A> {
    enum_tactic: E,
    else_tactic: T,
    item_tactic: A,
    short_circuiting: bool,
    _phantom_data: PhantomData<O>,
}

#[allow(dead_code)]
pub fn all_opt<O, E, T, A>(enum_tactic: E, else_tactic: T, item_tactic: A) -> AllOpt<O, E, T, A> {
    AllOpt {
        enum_tactic,
        else_tactic,
        item_tactic,
        short_circuiting: true,
        _phantom_data: PhantomData,
    }
}

impl<O, E, A, T> Statistics for AllOpt<O, E, T, A>
where
    A: Statistics,
{
    fn print_stats(&self) {
        self.item_tactic.print_stats();
    }
}

impl<E, A, I, O, C, T> Tactic<I, C> for AllOpt<O, E, T, A>
where
    E: OptEnumeratorTactic<I, O, C>,
    A: Tactic<O, C>,
    T: Tactic<I, C>,
{
    fn action(&mut self, data_in: &I, context: &C) -> DefaultProofNode {
        if let Some(iter) = self.enum_tactic.get_enumerator(data_in).iter(context) {
            let mut proof = DefaultProofNode::new_all(self.enum_tactic.msg(data_in));
            for d in iter {
                let res = if !self.item_tactic.precondition(&d, context) {
                    false
                } else {
                    let item_msg = self.enum_tactic.item_msg(&d);
                    let mut proof_item = self.item_tactic.action(&d, context);
                    proof_item = DefaultProofNode::new_info(item_msg, proof_item);
                    let outcome = proof_item.eval();
                    proof.add_child(proof_item);
                    outcome.success()
                };

                if !res && self.short_circuiting {
                    break;
                }
            }
            proof
        } else {
            self.else_tactic.action(data_in, context)
        }
    }

    fn precondition(&self, data: &I, context: &C) -> bool {
        self.enum_tactic.precondition(data, context)
    }
}

#[derive(Clone)]
pub struct All<O, E, A> {
    enum_tactic: E,
    item_tactic: A,
    short_circuiting: bool,
    _phantom_data: PhantomData<O>,
}

pub fn all<O, E, A>(enum_tactic: E, item_tactic: A) -> All<O, E, A> {
    All {
        enum_tactic,
        item_tactic,
        short_circuiting: true,
        _phantom_data: PhantomData,
    }
}

pub fn all_sc<O, E, A>(sc: bool, enum_tactic: E, item_tactic: A) -> All<O, E, A> {
    All {
        enum_tactic,
        item_tactic,
        short_circuiting: sc,
        _phantom_data: PhantomData,
    }
}

impl<O, E, A> Statistics for All<O, E, A>
where
    A: Statistics,
{
    fn print_stats(&self) {
        self.item_tactic.print_stats();
    }
}

impl<E, A, I, O, C> Tactic<I, C> for All<O, E, A>
where
    E: EnumeratorTactic<I, O, C>,
    A: Tactic<O, C>,
{
    fn action(&mut self, data_in: &I, context: &C) -> DefaultProofNode {
        let mut proof = DefaultProofNode::new_all(self.enum_tactic.msg(data_in));

        let enumerator = self.enum_tactic.get_enumerator(data_in);

        for d in enumerator.iter(context) {
            let res = if !self.item_tactic.precondition(&d, context) {
                false
            } else {
                let item_msg = self.enum_tactic.item_msg(&d);
                let mut proof_item = self.item_tactic.action(&d, context);
                proof_item = DefaultProofNode::new_info(item_msg, proof_item);
                let outcome = proof_item.eval();
                proof.add_child(proof_item);
                outcome.success()
            };

            if !res && self.short_circuiting {
                break;
            }
        }
        //}

        proof
    }

    fn precondition(&self, data: &I, context: &C) -> bool {
        self.enum_tactic.precondition(data, context)
    }
}

#[derive(Clone)]
pub struct Any<O, E, A> {
    enum_tactic: E,
    item_tactic: A,
    _phantom_data: PhantomData<O>,
}

pub fn any<O, E, A>(enumerator: E, tactic: A) -> Any<O, E, A> {
    Any {
        enum_tactic: enumerator,
        item_tactic: tactic,
        _phantom_data: PhantomData,
    }
}

impl<O, E, A> Statistics for Any<O, E, A>
where
    A: Statistics,
{
    fn print_stats(&self) {
        self.item_tactic.print_stats();
    }
}

impl<E, A, I, O, C> Tactic<I, C> for Any<O, E, A>
where
    E: EnumeratorTactic<I, O, C>,
    A: Tactic<O, C>,
{
    fn action(&mut self, data_in: &I, context: &C) -> DefaultProofNode {
        let mut proof = DefaultProofNode::new_any(self.enum_tactic.msg(data_in));

        let enumerator = self.enum_tactic.get_enumerator(data_in);
        enumerator.iter(context).any(|d| {
            if !self.item_tactic.precondition(&d, context) {
                false
            } else {
                let item_msg = self.enum_tactic.item_msg(&d);
                let mut proof_item = self.item_tactic.action(&d, context);
                proof_item = DefaultProofNode::new_info(item_msg, proof_item);
                let outcome = proof_item.eval();
                proof.add_child(proof_item);
                outcome.success()
            }
        });

        proof
    }

    fn precondition(&self, data: &I, context: &C) -> bool {
        self.enum_tactic.precondition(data, context)
    }
}
