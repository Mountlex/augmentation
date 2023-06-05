
// fn check_contractability(
//     instance: &Instance,
//     nodes_to_pidx: Vec<Option<Pidx>>,
//     finite: bool,
// ) -> Option<(Box<dyn Iterator<Item = InstPart>>, String)> {
//     let path_comps = instance.path_nodes().collect_vec();
//     let len = path_comps.len();

//     let all_edges = instance.all_edges();
//     let relevant_comps = path_comps
//         .iter()
//         .filter(|c| c.comp.is_c3() || c.comp.is_c4() || c.comp.is_c5() || c.comp.is_c6())
//         .cloned()
//         .collect_vec();
//     for i in 3..=3 {
//         // println!("Instance: {}", instance);
//         for pc in pseudo_cycles_of_length(
//             relevant_comps.clone(),
//             None,
//             all_edges.clone(),
//             vec![],
//             i,
//             false,
//         ) {
//             //  println!("{}", pc);
//             let mut vertices_sets = vec![vec![]];
//             for (n1, c, n2) in pc.cycle {
//                 let idx = c.to_idx();
//                 let comp = relevant_comps
//                     .iter()
//                     .find(|comp| comp.path_idx == idx)
//                     .unwrap();
//                 if n1 == n2 {
//                     vertices_sets.iter_mut().for_each(|set| set.push(n1));
//                 } else if comp.comp.is_adjacent(&n1, &n2) {
//                     vertices_sets.iter_mut().for_each(|set| {
//                         set.append(&mut comp.comp.nodes().iter().cloned().collect_vec())
//                     });
//                 } else {
//                     let (p1, p2) = comp.comp.paths_between(&n1, &n2);
//                     // println!("set {:?}, p1 {:?}, p2 {:?}", vertices_sets, p1, p2);
//                     vertices_sets = vertices_sets
//                         .into_iter()
//                         .flat_map(|set| {
//                             vec![
//                                 vec![set.clone(), p1.clone()].concat(),
//                                 vec![set, p2.clone()].concat(),
//                             ]
//                         })
//                         .collect_vec();
//                 }
//             }

//             for set in vertices_sets {
//                 if let Some(good_verts) = is_contractible(&set, instance) {
//                     // G[set] is contractible
//                     let all_nodes = instance
//                         .path_nodes()
//                         .flat_map(|c| c.comp.matching_nodes())
//                         .filter(|n| !set.contains(n) || good_verts.contains(n))
//                         .cloned()
//                         .collect_vec();

//                     // We now enumerate all edges which potentially resolve the contractability. Those are between the good vertices and
//                     // (all vertices / bad vertices) (including good vertices)
//                     let iter = edge_iterator(good_verts, all_nodes, true, !finite).unwrap();

//                     let iter = to_cases(iter, nodes_to_pidx, instance);
//                     //println!("iter: {}", iter.iter().join(", "));
//                     return Some((
//                         Box::new(iter),
//                         format!("Contractablility of large set {:?}", set),
//                     ));
//                 }
//             }
//         }
//     }
//     return None;
// }