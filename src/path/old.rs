fn print_path_statistics(proof: &PathProofNode) {
    let mut profiles = vec![];
    proof.get_payloads(&mut profiles);
    let mut profiles = profiles.into_iter().unique().collect_vec();

    let p_copy = profiles.clone();

    profiles.drain_filter(|p| {
        p.success
            && p_copy
                .iter()
                .any(|p2| p.comp_types == p2.comp_types && !p2.success)
    });
    profiles.drain_filter(|p| !p.success);

    let p_copy = profiles.clone();
    profiles.drain_filter(|p| p_copy.iter().any(|p2| p2.includes(p)));

    for profile in profiles {
        println!("{}", profile);
    }
}


// fn inductive_proof(options: PathProofOptions, depth: u8) -> Expression {
//     if depth > 0 {
//         induction_step(options, inductive_proof(options, depth - 1))
//     } else {
//         or(expr(Tactic::Print), expr(Tactic::TacticsExhausted(false)))
//     }
// }

// fn induction_step(options: PathProofOptions, step: Expression) -> Expression {
//     and(
//         // finite case
//         map(
//             Mapper::ToFiniteInstance,
//             or3(
//                 expr(Tactic::Print),
//                 //expr(Tactic::FilterInfinite),
//                 progress(true),
//                 find_all_edges_and_progress(
//                     options.edge_depth,
//                     true,
//                     or(expr(Tactic::Print), expr(Tactic::TacticsExhausted(true))),
//                 ),
//             ),
//         ), // infinite case
//         all_opt(
//             OptEnumerator::PathNode,
//             or3(
//                 expr(Tactic::Print),
//                 progress(false),
//                 find_all_edges_and_progress(options.edge_depth, false, step),
//             ),
//             or(expr(Tactic::Print), expr(Tactic::TacticsExhausted(false))),
//             options.sc,
//         ),
//     )
// }

// fn find_all_edges_and_progress(depth: u8, finite: bool, otherwise: Expression) -> Expression {
//     if depth > 0 {
//         find_edge_and_progress(
//             find_all_edges_and_progress(depth - 1, finite, otherwise.clone()),
//             finite,
//             otherwise,
//         )
//     } else {
//         otherwise
//     }
// }

// fn find_edge_and_progress(
//     enumerator: Expression,
//     finite: bool,
//     otherwise: Expression,
// ) -> Expression {
//     all_opt(
//         OptEnumerator::Edges(finite),
//         or(progress(finite), enumerator),
//         otherwise,
//         true,
//     )
// }