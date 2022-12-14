use itertools::{iproduct, Itertools};

use crate::{
    path::{
        proof::PathContext, AugmentedPathInstance, CycleEdge, Pidx, PseudoCycle,
        PseudoCycleInstance, SelectedHitInstance, SuperNode,
    },
    proof_logic::{Enumerator, EnumeratorTactic},
    types::Edge,
};

#[derive(Clone)]
pub struct PseudoCyclesEnum;

pub struct PseudoCyclesEnumerator<'a> {
    input: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<PseudoCycleInstance, PathContext> for PseudoCyclesEnumerator<'a> {
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = PseudoCycleInstance> + '_> {
        let instance = self.input;

        let matching_edges_iter = self
            .input
            .abstract_edges
            .iter()
            .filter(|m_edge| m_edge.is_cycle_edge().is_some())
            .flat_map(move |cycle_edge| {
                let (i, j) = cycle_edge.is_cycle_edge().unwrap();
                assert!(i < j);
                let mut pseudo_nodes = instance.nodes.as_slice()[i.raw()..=j.raw()].to_vec();

                pseudo_nodes
                    .first_mut()
                    .unwrap()
                    .get_zoomed_mut()
                    .set_out(cycle_edge.source());
                pseudo_nodes
                    .last_mut()
                    .unwrap()
                    .get_abstract_mut()
                    .nice_pair = false;

                let mut path_iter: Box<dyn Iterator<Item = Vec<SuperNode>>> =
                    Box::new(vec![pseudo_nodes].into_iter());
                for (k, l) in (i.raw()..=j.raw()).tuple_windows() {
                    path_iter = Box::new(path_iter.into_iter().flat_map(move |nodes| {
                        let pk = k - i.raw();
                        let pl = l - i.raw();
                        let nodes_clone = nodes.clone();
                        instance
                            .fixed_edges_between(k.into(), l.into())
                            .into_iter()
                            .map(move |path_edge| {
                                let mut nodes = nodes.clone();
                                nodes[pk]
                                    .get_zoomed_mut()
                                    .set_in(path_edge.endpoint_at(k.into()).unwrap());
                                nodes[pl]
                                    .get_zoomed_mut()
                                    .set_out(path_edge.endpoint_at(l.into()).unwrap());
                                nodes
                            })
                            .chain(vec![nodes_clone].into_iter())
                    }));
                }

                path_iter.map(move |nodes| {
                    let cycle = PseudoCycle { nodes };

                    PseudoCycleInstance {
                        instance: self.input.clone(),
                        cycle_edge: CycleEdge::Matching(cycle_edge.clone()),
                        pseudo_cycle: cycle,
                    }
                })
            });

        let mut iter: Box<dyn Iterator<Item = PseudoCycleInstance>> = Box::new(matching_edges_iter);
        for i in 3..=instance.path_len() {
            let fixed_edge_iter = pseudo_cycles_of_length(instance.clone(), i);
            iter = Box::new(iter.chain(fixed_edge_iter))
        }
        iter
    }
}

fn product_of_first(
    mut edges: Vec<Vec<Edge>>,
    length: usize,
) -> Box<dyn Iterator<Item = Vec<Edge>>> {
    assert_eq!(length, edges.len());
    if length == 6 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);
        let edges5 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4, edges5)
                .map(|(e1, e2, e3, e4, e5, e6)| vec![e1, e2, e3, e4, e5, e6]),
        )
    } else if length == 5 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);
        let edges4 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3, edges4)
                .map(|(e1, e2, e3, e4, e5)| vec![e1, e2, e3, e4, e5]),
        )
    } else if length == 4 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);
        let edges3 = edges.remove(0);

        Box::new(
            iproduct!(edges0, edges1, edges2, edges3).map(|(e1, e2, e3, e4)| vec![e1, e2, e3, e4]),
        )
    } else if length == 3 {
        let edges0 = edges.remove(0);
        let edges1 = edges.remove(0);
        let edges2 = edges.remove(0);

        Box::new(iproduct!(edges0, edges1, edges2).map(|(e1, e2, e3)| vec![e1, e2, e3]))
    } else {
        panic!()
    }
}

fn pseudo_cycles_of_length(
    instance: AugmentedPathInstance,
    length: usize,
) -> impl Iterator<Item = PseudoCycleInstance> {
    Pidx::range(instance.path_len())
        .into_iter()
        .permutations(length)
        .filter(|perm| perm.iter().min() == perm.first())
        .flat_map(move |perm| {
            let first = perm[0];
            let cons_edges = vec![perm.clone(), vec![first]]
                .concat()
                .windows(2)
                .map(|e| instance.fixed_edges_between(e[0], e[1]))
                .collect_vec();
            let instance = instance.clone();

            product_of_first(cons_edges, length).map(move |e| {
                let mut cycle_nodes = perm.iter().map(|i| instance[*i].clone()).collect_vec();

                for i in 0..length {
                    let last_edge = if i == 0 { length - 1 } else { i - 1 };
                    cycle_nodes[i]
                        .get_zoomed_mut()
                        .set_in(e[last_edge].endpoint_at(perm[i]).unwrap());
                    cycle_nodes[i]
                        .get_zoomed_mut()
                        .set_out(e[i].endpoint_at(perm[i]).unwrap());
                }

                // cycle nodes:   [0.out -- 1.in:1.out -- 2.in:2.out -- 3.in:3.out -- 0.in]

                let cycle = PseudoCycle { nodes: cycle_nodes };

                PseudoCycleInstance {
                    instance: instance.clone(),
                    cycle_edge: CycleEdge::Fixed,
                    pseudo_cycle: cycle,
                }
            })
        })
}

impl EnumeratorTactic<AugmentedPathInstance, PseudoCycleInstance, PathContext>
    for PseudoCyclesEnum
{
    type Enumer<'a> = PseudoCyclesEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &AugmentedPathInstance) -> String {
        format!("Enumerate all pseudo cycles")
    }

    fn item_msg(&self, item: &PseudoCycleInstance) -> String {
        format!(
            "Pseudo cycle via cycle edge [{}]",
            item.pseudo_cycle
                .nodes
                .iter()
                .map(|n| n.path_idx())
                .join(", ")
        )
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        PseudoCyclesEnumerator { input: data }
    }
}

impl EnumeratorTactic<SelectedHitInstance, PseudoCycleInstance, PathContext> for PseudoCyclesEnum {
    type Enumer<'a> = PseudoCyclesEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &SelectedHitInstance) -> String {
        format!("Enumerate all pseudo cycles")
    }

    fn item_msg(&self, item: &PseudoCycleInstance) -> String {
        format!(
            "Pseudo cycle via cycle edge [{}]",
            item.pseudo_cycle
                .nodes
                .iter()
                .map(|n| n.path_idx())
                .join(", ")
        )
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        PseudoCyclesEnumerator {
            input: &data.instance,
        }
    }
}
