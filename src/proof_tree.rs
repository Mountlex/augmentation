use std::fmt::{self, Display, Write};

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Outcome {
    True,
    False,
    Tight,
}

impl Outcome {
    pub fn success(&self) -> bool {
        !matches!(self, Outcome::False)
    }

    #[allow(dead_code)]
    pub fn tight(&self) -> bool {
        matches!(self, Outcome::Tight)
    }
}

#[derive(Clone)]
pub struct InnerNode<T> {
    msg: String,
    payload: Option<T>,
    outcome: Option<Outcome>,
    childs: Vec<ProofNode<T>>,
}
#[derive(Clone)]
pub struct OrNode<T> {
    outcome: Option<Outcome>,
    child1: Box<ProofNode<T>>,
    child2: Box<ProofNode<T>>,
}
#[derive(Clone)]
pub struct InfoNode<T> {
    msg: String,
    payload: Option<T>,
    outcome: Option<Outcome>,
    child: Box<ProofNode<T>>,
}

#[derive(Clone)]
pub struct LeafNode<T> {
    msg: String,
    payload: Option<T>,
    outcome: Outcome,
}

pub type DefaultProofNode = ProofNode<()>;

#[derive(Clone)]
pub enum ProofNode<T> {
    Leaf(LeafNode<T>),
    Info(InfoNode<T>),
    All(InnerNode<T>),
    Or(OrNode<T>),
    Any(InnerNode<T>),
}

impl<T: Clone> ProofNode<T> {
    pub fn new_leaf(msg: String, success: bool) -> Self {
        if success {
            ProofNode::Leaf(LeafNode {
                msg,
                payload: None,
                outcome: Outcome::True,
            })
        } else {
            ProofNode::Leaf(LeafNode {
                msg,
                payload: None,
                outcome: Outcome::False,
            })
        }
    }

    pub fn new_leaf_success(msg: String, tight: bool) -> Self {
        if tight {
            ProofNode::Leaf(LeafNode {
                msg,
                payload: None,
                outcome: Outcome::Tight,
            })
        } else {
            ProofNode::Leaf(LeafNode {
                msg,
                payload: None,
                outcome: Outcome::True,
            })
        }
    }

    pub fn new_all(msg: String) -> Self {
        ProofNode::All(InnerNode {
            msg,
            payload: None,
            outcome: None,
            childs: vec![],
        })
    }

    pub fn new_any(msg: String) -> Self {
        ProofNode::Any(InnerNode {
            msg,
            payload: None,
            outcome: None,
            childs: vec![],
        })
    }

    pub fn new_info(msg: String, child: ProofNode<T>) -> Self {
        ProofNode::Info(InfoNode {
            msg,
            outcome: None,
            payload: None,
            child: child.into(),
        })
    }

    pub fn new_or(child1: ProofNode<T>, child2: ProofNode<T>) -> Self {
        ProofNode::Or(OrNode {
            outcome: None,
            child1: child1.into(),
            child2: child2.into(),
        })
    }

    pub fn new_and(child1: ProofNode<T>, child2: ProofNode<T>) -> Self {
        ProofNode::All(InnerNode {
            msg: "and".into(),
            payload: None,
            outcome: None,
            childs: vec![child1, child2],
        })
    }

    pub fn outcome(&self) -> Outcome {
        match self {
            ProofNode::Leaf(node) => node.outcome,
            ProofNode::All(node) | ProofNode::Any(node) => node.outcome.unwrap(),
            ProofNode::Info(node) => node.outcome.unwrap(),
            ProofNode::Or(node) => node.outcome.unwrap(),
        }
    }

    pub fn success(&self) -> bool {
        match self {
            ProofNode::Leaf(node) => node.outcome.success(),
            ProofNode::All(node) | ProofNode::Any(node) => node.outcome.unwrap().success(),
            ProofNode::Info(node) => node.outcome.unwrap().success(),
            ProofNode::Or(node) => node.outcome.unwrap().success(),
        }
    }

    pub fn add_payload(&mut self, payload: T) {
        match self {
            ProofNode::Leaf(node) => node.payload = Some(payload),
            ProofNode::Info(node) => node.payload = Some(payload),
            ProofNode::All(node) => node.payload = Some(payload),
            ProofNode::Any(node) => node.payload = Some(payload),
            _ => {}
        }
    }

    pub fn add_child(&mut self, child: ProofNode<T>) {
        match self {
            ProofNode::All(node) | ProofNode::Any(node) => node.childs.push(child),
            _ => panic!(),
        }
    }

    pub fn get_payloads(&self, payloads: &mut Vec<T>) {
        let payload = match self {
            ProofNode::Leaf(node) => &node.payload,
            ProofNode::Info(node) => &node.payload,
            ProofNode::All(node) => &node.payload,
            ProofNode::Any(node) => &node.payload,
            _ => &None,
        };

        if let Some(payload) = payload {
            payloads.push(payload.clone())
        }

        match self {
            ProofNode::All(node) => node.childs.iter().for_each(|n| n.get_payloads(payloads)),
            ProofNode::Any(node) => node.childs.iter().for_each(|n| n.get_payloads(payloads)),
            ProofNode::Or(node) => {
                node.child1.get_payloads(payloads);
                node.child2.get_payloads(payloads);
            }
            ProofNode::Info(node) => node.child.get_payloads(payloads),
            ProofNode::Leaf(_) => {}
        }
    }

    pub fn eval_and_prune(&mut self) -> Outcome {
        match self {
            ProofNode::Leaf(node) => node.outcome,
            ProofNode::Info(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                node.outcome = Some(node.child.eval());
                node.outcome.unwrap()
            }
            ProofNode::All(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                node.outcome = Some(Outcome::True);
                for c in &mut node.childs {
                    match c.eval() {
                        Outcome::False => node.outcome = Some(Outcome::False),
                        Outcome::Tight if node.outcome == Some(Outcome::True) => {
                            node.outcome = Some(Outcome::Tight)
                        }
                        _ => {}
                    }
                }
                let outcome = node.outcome.unwrap();
                if outcome.success() || node.msg == "pc" {
                    node.childs.clear();
                }
                outcome
            }
            ProofNode::Any(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                node.outcome = Some(Outcome::False);
                for c in &mut node.childs {
                    match c.eval() {
                        Outcome::Tight => node.outcome = Some(Outcome::Tight),
                        Outcome::True if node.outcome == Some(Outcome::False) => {
                            node.outcome = Some(Outcome::True)
                        }
                        _ => {}
                    }
                }
                let outcome = node.outcome.unwrap();
                if outcome.success() || node.msg == "pc" {
                    node.childs.clear();
                }
                outcome
            }
            ProofNode::Or(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                let r1 = node.child1.eval();
                let r2 = node.child2.eval();

                node.outcome = match (r1, r2) {
                    (Outcome::Tight, _) | (_, Outcome::Tight) => Some(Outcome::Tight),
                    (Outcome::True, _) | (_, Outcome::True) => Some(Outcome::True),
                    _ => Some(Outcome::False),
                };

                node.outcome.unwrap()
            }
        }
    }

    pub fn eval(&mut self) -> Outcome {
        match self {
            ProofNode::Leaf(node) => node.outcome,
            ProofNode::Info(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                node.outcome = Some(node.child.eval());
                node.outcome.unwrap()
            }
            ProofNode::All(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                node.outcome = Some(Outcome::True);
                for c in &mut node.childs {
                    match c.eval() {
                        Outcome::False => node.outcome = Some(Outcome::False),
                        Outcome::Tight if node.outcome == Some(Outcome::True) => {
                            node.outcome = Some(Outcome::Tight)
                        }
                        _ => {}
                    }
                }
                node.outcome.unwrap()
            }
            ProofNode::Any(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                node.outcome = Some(Outcome::False);
                for c in &mut node.childs {
                    match c.eval() {
                        Outcome::Tight => node.outcome = Some(Outcome::Tight),
                        Outcome::True if node.outcome == Some(Outcome::False) => {
                            node.outcome = Some(Outcome::True)
                        }
                        _ => {}
                    }
                }
                node.outcome.unwrap()
            }
            ProofNode::Or(node) => {
                if let Some(s) = node.outcome {
                    return s;
                }
                let r1 = node.child1.eval();
                let r2 = node.child2.eval();

                node.outcome = match (r1, r2) {
                    (Outcome::Tight, _) | (_, Outcome::Tight) => Some(Outcome::Tight),
                    (Outcome::True, _) | (_, Outcome::True) => Some(Outcome::True),
                    _ => Some(Outcome::False),
                };

                node.outcome.unwrap()
            }
        }
    }

    pub fn is_msg_empty(&self) -> bool {
        match self {
            ProofNode::Leaf(node) => node.msg.is_empty(),
            ProofNode::Info(node) => node.msg.is_empty(),
            ProofNode::All(node) => node.msg.is_empty(),
            ProofNode::Or(_) => true,
            ProofNode::Any(node) => node.msg.is_empty(),
        }
    }

    fn msg(&self) -> String {
        format!("{}", self)
    }

    pub fn print_tree<W: Write>(
        &self,
        writer: &mut W,
        max_depth_true: usize,
    ) -> anyhow::Result<()> {
        self.print_tree_rec(writer, 0, max_depth_true)
    }

    fn print_tree_rec<W: Write>(
        &self,
        writer: &mut W,
        depth: usize,
        max_depth_true: usize,
    ) -> anyhow::Result<()> {
        let mut new_depth = depth;
        match self {
            ProofNode::Leaf(_) | ProofNode::Info(_) => {
                //| ProofNode::All(_) | ProofNode::Any(_) => {
                if !self.is_msg_empty() {
                    new_depth += 1;
                    (0..depth).try_for_each(|_| write!(writer, "  "))?;
                    writeln!(writer, "{}", self.msg())?;
                }
            }
            _ => { // dont print or's
            }
        }

        match &self {
            ProofNode::Leaf(_) => {}
            ProofNode::Info(node) => {
                let c = &node.child;
                if !(c.outcome().success() && depth >= max_depth_true) {
                    c.print_tree_rec(writer, new_depth, max_depth_true)?;
                }
            }
            ProofNode::Or(node) => {
                let c1 = &node.child1;
                if !(c1.outcome().success() && depth >= max_depth_true) {
                    c1.print_tree_rec(writer, new_depth, max_depth_true)?;
                }
                let c2 = &node.child2;
                if !(c2.outcome().success() && depth >= max_depth_true) {
                    c2.print_tree_rec(writer, new_depth, max_depth_true)?;
                }
            }
            ProofNode::All(node) | ProofNode::Any(node) => {
                for c in &node.childs {
                    if !(c.outcome().success() && depth >= max_depth_true) {
                        c.print_tree_rec(writer, new_depth, max_depth_true)?;
                    }
                }
            }
        }

        Ok(())
    }
}

impl<T> Display for ProofNode<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofNode::Leaf(node) => match node.outcome {
                Outcome::True => write!(f, "{} ✔️", node.msg),
                Outcome::Tight => write!(f, "{} =✔️=", node.msg),
                Outcome::False => write!(f, "{} ❌", node.msg),
            },
            ProofNode::Info(node) => match node.outcome.unwrap() {
                Outcome::True => write!(f, "{} ✔️", node.msg),
                Outcome::Tight => write!(f, "{} =✔️=", node.msg),
                Outcome::False => write!(f, "{} ❌", node.msg),
            },
            ProofNode::All(node) | ProofNode::Any(node) => match node.outcome.unwrap() {
                Outcome::True => write!(f, "{} ✔️", node.msg),
                Outcome::Tight => write!(f, "{} =✔️=", node.msg),
                Outcome::False => write!(f, "{} ❌", node.msg),
            },
            ProofNode::Or(_) => todo!(),
        }
    }
}
