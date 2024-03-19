use std::fmt::Display;

use itertools::Itertools;

use crate::{Credit, Node};

use super::Pidx;

#[derive(Clone, Debug)]
pub struct PseudoCycle {
    pub cycle: Vec<(Node, CycleComp, Node)>,
    pub total_edge_cost: Credit,
}

impl PseudoCycle {
    pub fn consecutive_end(&self) -> bool {
        let mut indices = self
            .cycle
            .iter()
            .flat_map(|(_, cycle_comp, _)| {
                if let CycleComp::PathComp(idx) = cycle_comp {
                    Some(idx.raw())
                } else {
                    None
                }
            })
            .collect_vec();
        indices.sort();
        indices.contains(&0) && *indices.last().unwrap() == indices.len() - 1
    }
}

impl Display for PseudoCycle {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let inner = self
            .cycle
            .iter()
            .map(|(l, n, r)| match n {
                CycleComp::PathComp(idx) => format!("{}-[{}]-{}", l, idx, r),
                CycleComp::Rem => "REM".to_string(),
            })
            .join(", ");
        write!(f, "PC [ {} ] (length={})", inner, self.cycle.len())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum CycleComp {
    PathComp(Pidx),
    Rem,
}

impl CycleComp {
    pub fn to_idx(&self) -> Pidx {
        match self {
            CycleComp::PathComp(idx) => *idx,
            CycleComp::Rem => panic!("Rem has no idx"),
        }
    }

    pub fn is_rem(&self) -> bool {
        matches!(self, CycleComp::Rem)
    }
}

impl Display for CycleComp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CycleComp::PathComp(idx) => write!(f, "{}", idx),
            CycleComp::Rem => write!(f, "REM"),
        }
    }
}
