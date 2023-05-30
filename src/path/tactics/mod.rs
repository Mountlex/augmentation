use itertools::Itertools;

use super::{instance::Instance, PathProofNode};
use crate::logic::TacticTrait;

mod contract;
mod cycle_merge;
mod cycle_rearrange;
mod local_merge;
mod longer_path;
mod pendant_rewire;

pub use cycle_rearrange::check_fixed_extension_feasible;

#[derive(Debug, Clone)]
pub enum Tactic {
    LongerPath(bool),
    CycleMerge,
    LocalMerge,
    Rearrangable(bool),
    Contractable,
    Pendant,
    TacticsExhausted(bool),
}

impl TacticTrait for Tactic {
    type Inst = Instance;

    fn prove(&self, stack: &mut Instance) -> PathProofNode {
        let proof = match self {
            Tactic::LongerPath(finite) => longer_path::check_longer_nice_path(stack, *finite),
            Tactic::CycleMerge => cycle_merge::check_cycle_merge(stack),
            Tactic::LocalMerge => local_merge::check_local_merge(stack),
            Tactic::Rearrangable(finite) => {
                cycle_rearrange::check_path_rearrangement(stack, *finite)
            }
            Tactic::Contractable => contract::check_contractability(stack),
            Tactic::Pendant => pendant_rewire::check_pendant_node(stack),
            Tactic::TacticsExhausted(finite) => {
                let all_edges = stack.all_edges();
                let outside = stack.out_edges();
                let path_comps = stack.path_nodes().collect_vec();
                let rem_edges = stack.rem_edges();

                //  println!("{}", stack.get_profile(true));

                let msg = format!(
                    "Instance: [{}][{}][{}][{}]",
                    path_comps.iter().join(", "),
                    all_edges.iter().join(","),
                    outside.iter().join(","),
                    rem_edges.iter().join(",")
                );

                if *finite {
                    log::info!("tactics (finite) exhausted for: {}", msg);
                    PathProofNode::new_leaf("Tactics (finite) exhausted!".into(), false)
                } else {
                    log::info!("tactics exhausted for: {}", msg);
                    PathProofNode::new_leaf("Tactics exhausted!".into(), false)
                }
            } // Tactic::Print => {
              //     let all_edges = stack.all_edges();
              //     let outside = stack.out_edges();
              //     let path_comps = stack.path_nodes().collect_vec();
              //     let rem_edges = stack.rem_edges();

              //     //  println!("{}", stack.get_profile(true));

              //     let msg = format!(
              //         "Instance: [{}][{}][{}][{}]",
              //         path_comps.iter().join(", "),
              //         all_edges.iter().join(","),
              //         outside.iter().join(","),
              //         rem_edges.iter().join(",")
              //     );

              //     PathProofNode::new_leaf(msg, false)
              // }
        };
        proof
    }
}
