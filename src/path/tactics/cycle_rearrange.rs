use crate::{
    path::{
        proof::PathContext, AugmentedPathInstance, CycleEdge, PathRearrangementInstance, SuperNode,
    },
    proof_logic::{Statistics, Tactic},
    proof_tree::ProofNode,
};

#[derive(Clone)]
pub struct CycleRearrangeTactic {
    num_calls: usize,
    num_proofs: usize,
}

impl CycleRearrangeTactic {
    pub fn new() -> Self {
        Self {
            num_calls: 0,
            num_proofs: 0,
        }
    }
}

impl Statistics for CycleRearrangeTactic {
    fn print_stats(&self) {
        println!("Cycle rearrange {} / {}", self.num_proofs, self.num_calls);
    }
}

impl Tactic<PathRearrangementInstance, PathContext> for CycleRearrangeTactic {
    fn action(&mut self, data: &PathRearrangementInstance, _context: &PathContext) -> ProofNode {
        self.num_calls += 1;

        let mut feasible =
            check_fixed_extension_feasible(&data.extension, &data.instance, true);
        feasible.eval();
        if !feasible.success() {
            return feasible;
        } else {
            let old_last_node = data
                .extension
                .iter()
                .find(|n| n.path_idx().is_last())
                .unwrap()
                .get_zoomed();
            let old_last_comp = old_last_node.get_comp();

            let new_last = data.extension.last().unwrap();
            let new_last_comp = new_last.get_comp();

            // Complex > C5 > C4 > Large > C7 > C6 > C3

            // Reduce C3 to anything except C3
            if old_last_comp.is_c3() && !new_last_comp.is_c3() {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!("Rearrange cycle: now ends with {}!", new_last_comp),
                    true,
                );
            }

            // Reduce C6 to anything except C3 and C6
            if old_last_comp.is_c6() && !new_last_comp.is_c3() && !new_last_comp.is_c6() {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!("Rearrange cycle: now ends with {}!", new_last_comp),
                    true,
                );
            }

            // Reduce C6 to anything except C3 and C6 and C7
            if old_last_comp.is_c7()
                && !new_last_comp.is_c3()
                && !new_last_comp.is_c6()
                && !new_last_comp.is_c7()
            {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!("Rearrange cycle: now ends with {}!", new_last_comp),
                    true,
                );
            }

            // Reduce Large to anything except C3 and C6 and C7 and Large
            if old_last_comp.is_large()
                && !new_last_comp.is_large()
                && !new_last_comp.is_c3()
                && !new_last_comp.is_c6()
                && !new_last_comp.is_c7()
            {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!("Rearrange cycle: now ends with {}!", new_last_comp),
                    true,
                );
            }

            // Reduce C4 to C5
            if old_last_comp.is_c4() && new_last_comp.is_c5() {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!("Rearrange cycle: now ends with {}!", new_last_comp),
                    true,
                );
            }

            // Reduce anything that is not complex to complex
            if !old_last_comp.is_complex() && new_last_comp.is_complex() {
                self.num_proofs += 1;
                return ProofNode::new_leaf(
                    format!("Rearrange cycle: now ends with {}!", new_last_comp),
                    true,
                );
            }

            return ProofNode::new_leaf(format!("No feasible reduction"), false);
        }
    }

    fn precondition(&self, data: &PathRearrangementInstance, _context: &PathContext) -> bool {
        !data.extension.iter().any(|n| matches!(n, SuperNode::RemPath(_)))
    }
}

pub fn check_fixed_extension_feasible(
    extension: &[SuperNode],
    instance: &AugmentedPathInstance,
    prelast_is_prelast: bool,
) -> ProofNode {
    // extension:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in]

    // check for inner zoomed nodes of extension that they fullfil nice path properties
    for i in 1..extension.len() - 1 {
        let inner_node = &extension[i];
        if let SuperNode::Zoomed(node) = inner_node {
            let valid_in_out = node.valid_in_out(
                node.in_node.unwrap(),
                node.out_node.unwrap(),
                i == extension.len() - 2 && prelast_is_prelast,
            );
            if !valid_in_out {
                return ProofNode::new_leaf(
                    format!("New path does not fulfill nice path properties!"),
                    false,
                )
                .into();
            }
        }
    }

    if let Some(SuperNode::Abstract(node)) = extension.get(extension.len() - 2) {
        if node.get_comp().is_c5() {
            return ProofNode::new_leaf(
                format!("New prelast is C5 but we cannot check nice path properties",),
                false,
            )
            .into();
        }
    } 

    // check for inner abstract nodes if we do not care about nice pairs
    for i in 1..extension.len() - 1 {
        let inner_node = &extension[i];
        if let SuperNode::Abstract(node) = inner_node {
            if (node.get_comp().is_c3() || node.get_comp().is_c4()) && !node.nice_pair {
                return ProofNode::new_leaf(
                    format!(
                        "Cannot rearrange cycle: comp {} is abstract but has no nice pair!",
                        node.get_comp()
                    ),
                    false,
                )
                .into();
            }
        }
    }


    // check that connection between hit and remaining path is feasible
    if let Some(SuperNode::Zoomed(hit_node)) = extension.first() {
        if let SuperNode::Zoomed(path_hit_node) = &instance[hit_node.path_idx] {
            if let Some(path_hit_in) = path_hit_node.in_node {
                if !hit_node.valid_in(path_hit_in, false) {
                    return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has no nice pair in new instance!", hit_node.get_comp()), false).into();
                }
            }
        }
    } 

    // check that connection between hit and remaining path is feasible
    if let Some(SuperNode::Abstract(node)) = extension.first() {
        if node.get_comp().is_c3() || node.get_comp().is_c4() {
            return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has no nice pair in new instance!", node.get_comp()), false).into();
        }
    } 


    ProofNode::new_leaf("Feasible path".into(), true)
}

fn check_matching_edge_extension_feasible(extension: &[SuperNode]) -> ProofNode {
    let old_last_node = extension
        .iter()
        .find(|n| n.path_idx().is_last())
        .unwrap()
        .get_zoomed();
    let old_last_comp = old_last_node.get_comp();

    let hit = extension.first().unwrap();

    // this is the case where we have an unexpanded matching edge

    // old_last --- ... --- new_prelast --- new_last --- hit --- rem_path
    //     |                                              |
    //     -----------------------------------------------|
    //                               matching edge

    let new_prelast = &extension[extension.len() - 2];
    let new_prelast_comp = new_prelast.get_comp();

    if new_prelast_comp.is_c5() {
        return ProofNode::new_leaf(
            format!("New prelast is C5 but we cannot check nice path properties",),
            false,
        )
        .into();
    }
    let old_last_np = old_last_node.npc.is_nice_pair(
        old_last_node.in_node.unwrap(),
        old_last_node.out_node.unwrap(),
    );

    if (old_last_comp.is_c3() || old_last_comp.is_c4()) && !old_last_np {
        return ProofNode::new_leaf(
            format!(
                "Cannot rearrange cycle: last comp is {} but has no nice pair!",
                old_last_comp
            ),
            false,
        )
        .into();
    }

    if let SuperNode::Abstract(hit_node) = hit {
        let hit_comp = hit_node.get_comp();

        if hit_comp.is_c3() || hit_comp.is_c4() {
            // Note that for aided C5 we dont have to ensure a nice pair, because it is not prelast.
            return ProofNode::new_leaf(format!("Cannot rearrange cycle: hit comp is {} but has nice pair in cycle, so we cannot guarantee nice pair on path!", hit_comp), false).into();
        }
    } else {
        panic!()
    }
    ProofNode::new_leaf("Feasbile path".into(), true)
}


