use itertools::Itertools;

use super::{instance::Instance, PathProofNode};
use crate::logic::TacticTrait;

mod cycle_merge;
mod cycle_rearrange;
mod local_merge;
mod longer_path;
mod pendant_rewire;


#[derive(Debug, Clone)]
pub enum Tactic {
    LongerPath(bool),
    FastLongerPath(bool),
    CycleMerge,
    LocalMerge,
    Rearrangable(bool),
    Pendant,
    TacticsExhausted(bool),
}

impl TacticTrait for Tactic {
    type Inst = Instance;

    fn prove(&self, stack: &mut Instance) -> PathProofNode {
        let proof = match self {
            Tactic::FastLongerPath(_finite) => {
                let outside = stack.out_edges();
                let path_comps = stack.path_nodes().collect_vec();
                let last = path_comps.first().unwrap();
                if (last.comp.is_c6() || last.comp.is_c7())
                    && outside.iter().any(|n| last.comp.contains(n))
                {
                    // if the last component is a c6 or c7, we can just extend the nice path, as we have no requirements on the in and out of c6 and c7s.                
                    return PathProofNode::new_leaf("fast_longer_path".into(), true);
                }
                PathProofNode::new_leaf("no fast_longer_path".into(), false)
            }
            Tactic::LongerPath(finite) => longer_path::check_longer_nice_path(stack, *finite),
            Tactic::CycleMerge => cycle_merge::check_cycle_merge(stack),
            Tactic::LocalMerge => local_merge::check_local_merge(stack),
            Tactic::Rearrangable(finite) => {
                cycle_rearrange::check_path_rearrangement(stack, *finite)
            }
            Tactic::Pendant => pendant_rewire::check_pendant_node(stack),
            Tactic::TacticsExhausted(finite) => {
                let all_edges = stack.all_edges();
                let outside = stack.out_edges();
                let path_comps = stack.path_nodes().collect_vec();
                let rem_edges = stack.rem_edges();

                let mut contract_checked = stack.contractability_checked();

                //  println!("{}", stack.get_profile(true));

                let msg = format!(
                    "Instance: [{}][{}] o=[{}] rem=[{}] contr=[{}] non_rem=[{}] all_rem=[{}]",
                    path_comps.iter().join(", "),
                    all_edges.iter().join(","),
                    outside.iter().join(","),
                    rem_edges.iter().join(","),
                    contract_checked.join(","),
                    stack.non_rem_edges().iter().join(","),
                    stack.all_rem_edges().iter().join(",")
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
