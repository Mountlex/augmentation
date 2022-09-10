use std::fmt::{self, Display, Write};

pub trait Tree<N>
where
    N: Tree<N>,
{
    fn childs(&self) -> Option<&[ProofNode]>;
    fn msg(&self) -> String;

    
}

pub enum ProofNode {
    Leaf {
        msg: String,
        success: bool,
    },
    Info {
        msg: String,
        success: Option<bool>,
        child: Vec<ProofNode>
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

    pub fn new_info(msg: String, child: ProofNode) -> Self {
        ProofNode::Info {
            msg,
            success: None,
            child: vec![child],
        }
    }

    pub fn success(&self) -> bool {
        match self {
            ProofNode::Leaf { msg, success } => *success,
            ProofNode::Info { msg, success, child } => success.unwrap().clone(),
            ProofNode::All { msg, success, childs } => success.unwrap().clone(),
            ProofNode::Any { msg, success, childs } => success.unwrap().clone(),
        }
    }

    pub fn add_child(&mut self, node: ProofNode) {
        match self {
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
            _ => panic!(),
        }
    }

    pub fn eval(&mut self) -> bool {
        match self {
            ProofNode::Leaf { msg: _, success } => *success,
            ProofNode::Info { msg: _, success, child } => {
                if let Some(s) = success {
                    return *s;
                }
                *success = Some(child.first_mut().unwrap().eval());
                success.unwrap().clone()
            },
            ProofNode::All {
                msg: _,
                success,
                childs,
            } => {
                if let Some(s) = success {
                    return *s;
                }
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
                if let Some(s) = success {
                    return *s;
                }
                *success = Some(false);
                for c in childs {
                    if c.eval() {
                    *success = Some(true);
                    }
                }
                success.unwrap().clone()
            }
        }
    }

    fn msg(&self) -> String {
        format!("{}", self)
    }

    fn childs(&self) -> Option<&[ProofNode]> {
        match self {
            ProofNode::Leaf { msg: _, success: _ } => None,
            ProofNode::Info { msg: _, success: _, child } => Some(child),
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

    pub fn print_tree<W: Write>(&self, writer: &mut W, depth: usize, max_depth_true: usize) -> anyhow::Result<()> {
        let mut new_depth = depth;
        match self {
            ProofNode::Leaf { msg:_, success:_ } | 
            ProofNode::Info { msg:_, success:_, child:_ } => {
                new_depth += 1;
                (0..depth).try_for_each(|_| write!(writer, "    "))?;
                writeln!(writer, "{}", self.msg())?;
            },
            _ => {
                new_depth += 1;
                (0..depth).try_for_each(|_| write!(writer, "    "))?;
                writeln!(writer, "{}", self.msg())?;
            }
        }
        if let Some(childs) = self.childs() {
            for c in childs {
                if !(c.success() && depth == max_depth_true) {
                    c.print_tree(writer, new_depth, max_depth_true)?;
                }
            }
        }
        Ok(())
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
            ProofNode::Info {
                msg,
                success,
                child: _,
            }
            |
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
