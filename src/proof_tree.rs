use std::fmt::{self, Display, Write};

pub trait Tree<N>
where
    N: Tree<N>,
{
    fn childs(&self) -> Option<&[ProofNode]>;
    fn msg(&self) -> String;

    fn print_tree<W: Write>(&self, writer: &mut W, depth: usize) -> anyhow::Result<()> {
        (0..depth).try_for_each(|_| write!(writer, "    "))?;
        writeln!(writer, "{}", self.msg())?;
        if let Some(childs) = self.childs() {
            for c in childs {
                c.print_tree(writer, depth + 1)?;
            }
        }
        Ok(())
    }
}

pub enum ProofNode {
    Leaf {
        msg: String,
        success: bool,
    },
    All {
        msg: String,
        success: Option<bool>,
        childs: Vec<ProofNode>,
    },
    Any {
        msg: String,
        success: Option<bool>,
        childs: Vec<ProofNode>,
    },
}

impl ProofNode {
    pub fn new_leaf(msg: String, success: bool) -> Self {
        ProofNode::Leaf { msg, success }
    }

    pub fn new_all(msg: String) -> Self {
        ProofNode::All {
            msg,
            success: None,
            childs: vec![],
        }
    }

    pub fn new_any(msg: String) -> Self {
        ProofNode::Any {
            msg,
            success: None,
            childs: vec![],
        }
    }

    pub fn add_child(&mut self, node: ProofNode) {
        match self {
            ProofNode::Leaf { msg: _, success: _ } => panic!(),
            ProofNode::All {
                msg: _,
                success: _,
                childs,
            } => childs.push(node),
            ProofNode::Any {
                msg: _,
                success: _,
                childs,
            } => childs.push(node),
        }
    }

    pub fn eval(&mut self) -> bool {
        match self {
            ProofNode::Leaf { msg: _, success } => *success,
            ProofNode::All {
                msg: _,
                success,
                childs,
            } => {
                *success = Some(true);
                for c in childs {
                    if !c.eval() {
                    *success = Some(false);
                    }
                }
                success.unwrap().clone()
            },
            ProofNode::Any {
                msg: _,
                success,
                childs,
            } => {
                *success = Some(childs.is_empty());
                for c in childs {
                    if c.eval() {
                    *success = Some(true);
                    }
                }
                success.unwrap().clone()
            }
        }
    }
}

impl Tree<ProofNode> for ProofNode {
    fn msg(&self) -> String {
        format!("{}", self)
    }

    fn childs(&self) -> Option<&[ProofNode]> {
        match self {
            ProofNode::Leaf { msg: _, success: _ } => None,
            ProofNode::All {
                msg: _,
                success: _,
                childs,
            }
            | ProofNode::Any {
                msg: _,
                success: _,
                childs,
            } => Some(childs),
        }
    }
}

impl Display for ProofNode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ProofNode::Leaf { msg, success } => {
                if *success {
                    write!(f, "{} ✔️", msg)
                } else {
                    write!(f, "{} ❌", msg)
                }
            },
            ProofNode::All {
                msg,
                success,
                childs: _,
            }
            | ProofNode::Any {
                msg,
                success,
                childs: _,
            } => {
                if success.unwrap() {
                    write!(f, "{} ✔️", msg)
                } else {
                    write!(f, "{} ❌", msg)
                }
            }
        }
    }
}
