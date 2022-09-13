use std::fmt::{self, Display, Write};

#[derive(Clone)]
struct InnerNode {
    msg: String,
    success: Option<bool>,
    childs: Vec<ProofNode>,
}
#[derive(Clone)]
struct OrNode {
    success: Option<bool>,
    child1: Box<ProofNode>,
    child2: Box<ProofNode>,
}
#[derive(Clone)]
struct InfoNode {
    msg: String,
    success: Option<bool>,
    child: Box<ProofNode>,
}
#[derive(Clone)]
struct LeafNode {
    msg: String,
    success: bool,
}

#[derive(Clone)]
pub enum ProofNode {
    Leaf(LeafNode),
    Info(InfoNode),
    All(InnerNode),
    Or(OrNode),
    Any(InnerNode),
}

impl ProofNode {
    pub fn new_leaf(msg: String, success: bool) -> Self {
        ProofNode::Leaf(LeafNode { msg, success })
    }

    pub fn new_all(msg: String) -> Self {
        ProofNode::All(InnerNode {
            msg,
            success: None,
            childs: vec![],
        })
    }

    pub fn new_any(msg: String) -> Self {
        ProofNode::Any(InnerNode {
            msg,
            success: None,
            childs: vec![],
        })
    }

    pub fn new_info(msg: String, child: ProofNode) -> Self {
        ProofNode::Info(InfoNode {
            msg,
            success: None,
            child: child.into(),
        })
    }

    pub fn new_or(child1: ProofNode, child2: ProofNode) -> Self {
        ProofNode::Or(OrNode {
            success: None,
            child1: child1.into(),
            child2: child2.into(),
        })
    }

    pub fn success(&self) -> bool {
        match self {
            ProofNode::Leaf(node) => node.success,
            ProofNode::All(node) | ProofNode::Any(node) => node.success.unwrap().clone(),
            ProofNode::Info(node) => node.success.unwrap().clone(),
            ProofNode::Or(node) => node.success.unwrap().clone(),
        }
    }

    pub fn add_child(&mut self, child: ProofNode) {
        match self {
            ProofNode::All(node) | ProofNode::Any(node) => node.childs.push(child),
            _ => panic!(),
        }
    }

    pub fn eval(&mut self) -> bool {
        match self {
            ProofNode::Leaf(node) => node.success,
            ProofNode::Info(node) => {
                if let Some(s) = node.success {
                    return s;
                }
                node.success = Some(node.child.eval());
                node.success.unwrap().clone()
            }
            ProofNode::All(node) => {
                if let Some(s) = node.success {
                    return s;
                }
                node.success = Some(true);
                for c in &mut node.childs {
                    if !c.eval() {
                        node.success = Some(false);
                    }
                }
                node.success.unwrap().clone()
            }
            ProofNode::Any(node) => {
                if let Some(s) = node.success {
                    return s;
                }
                node.success = Some(false);
                for c in &mut node.childs {
                    if c.eval() {
                        node.success = Some(true);
                    }
                }
                node.success.unwrap().clone()
            }
            ProofNode::Or(node) => {
                if let Some(s) = node.success {
                    return s;
                }
                let r1 = node.child1.eval();
                let r2 = node.child2.eval();
                node.success = Some(r1 || r2);
                r1 || r2
            }
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
            ProofNode::Leaf(_) | ProofNode::Info(_) | ProofNode::All(_) | ProofNode::Any(_) => {
                new_depth += 1;
                (0..depth).try_for_each(|_| write!(writer, "    "))?;
                writeln!(writer, "{}", self.msg())?;
            }
            _ => { // dont print or's
            }
        }

        match &self {
            ProofNode::Leaf(_) => {}
            ProofNode::Info(node) => {
                let c = &node.child;
                if !(c.success() && depth == max_depth_true) {
                    c.print_tree_rec(writer, new_depth, max_depth_true)?;
                }
            }
            ProofNode::Or(node) => {
                let c1 = &node.child1;
                if !(c1.success() && depth == max_depth_true) {
                    c1.print_tree_rec(writer, new_depth, max_depth_true)?;
                }
                let c2 = &node.child2;
                if !(c2.success() && depth == max_depth_true) {
                    c2.print_tree_rec(writer, new_depth, max_depth_true)?;
                }
            }
            ProofNode::All(node) | ProofNode::Any(node) => {
                for c in &node.childs {
                    if !(c.success() && depth == max_depth_true) {
                        c.print_tree_rec(writer, new_depth, max_depth_true)?;
                    }
                }
            }
        }

        Ok(())
    }
}

impl Display for ProofNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofNode::Leaf(node) => {
                if node.success {
                    write!(f, "{} ✔️", node.msg)
                } else {
                    write!(f, "{} ❌", node.msg)
                }
            }
            ProofNode::Info(node) => {
                if node.success.unwrap() {
                    write!(f, "{} ✔️", node.msg)
                } else {
                    write!(f, "{} ❌", node.msg)
                }
            }
            ProofNode::All(node) | ProofNode::Any(node) => {
                if node.success.unwrap() {
                    write!(f, "{} ✔️", node.msg)
                } else {
                    write!(f, "{} ❌", node.msg)
                }
            }
            ProofNode::Or(_) => todo!(),
        }
    }
}
