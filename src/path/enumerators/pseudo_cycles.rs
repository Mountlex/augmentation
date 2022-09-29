
use itertools::Itertools;

use crate::{
    path::{
        proof::PathContext, AugmentedPathInstance, CycleEdge, PseudoCycle, PseudoCycleInstance,
        SelectedHitInstance, SuperNode,
    },
    proof_logic::{Enumerator, EnumeratorTactic},
};

#[derive(Clone)]
pub struct PseudoCyclesEnum;

pub struct PseudoCyclesEnumerator<'a> {
    input: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<PseudoCycleInstance, PathContext> for PseudoCyclesEnumerator<'a> {
    fn iter(&self, _context: &PathContext) -> Box<dyn Iterator<Item = PseudoCycleInstance> + '_> {
        let path = &self.input.path;
        let instance = self.input;

        let matching_edges_iter = self
            .input
            .non_path_matching_edges
            .iter()
            .filter(|m_edge| m_edge.is_cycle_edge().is_some())
            .flat_map(move |cycle_edge| {
                let (i, j) = cycle_edge.is_cycle_edge().unwrap();
                let mut pseudo_nodes = self.input.path.nodes.as_slice()[i..=j].to_vec();

                pseudo_nodes.last_mut().unwrap().get_zoomed_mut().out_node =
                    Some(cycle_edge.source());
                pseudo_nodes
                    .first_mut()
                    .unwrap()
                    .get_abstract_mut()
                    .nice_pair = false;

                let mut path_iter: Box<dyn Iterator<Item = Vec<SuperNode>>> =
                    Box::new(vec![pseudo_nodes].into_iter());
                for (k, l) in (i..=j).tuple_windows() {
                    path_iter = Box::new(path_iter.into_iter().flat_map(move |nodes| {
                        let pk = k - i;
                        let pl = l - i;
                        let nodes_clone = nodes.clone();
                        instance
                            .fixed_edges_between(k, l)
                            .into_iter()
                            .map(move |path_edge| {
                                let mut nodes = nodes.clone();
                                nodes[pk].get_zoomed_mut().out_node = Some(path_edge.0);
                                nodes[pl].get_zoomed_mut().in_node = Some(path_edge.1);
                                nodes
                            })
                            .chain(vec![nodes_clone].into_iter())
                    }));
                }

                path_iter.map(|nodes| {
                    let cycle = PseudoCycle { nodes };

                    PseudoCycleInstance {
                        path_matching: self.input.clone(),
                        cycle_edge: CycleEdge::Matching(cycle_edge.clone()),
                        pseudo_cycle: cycle,
                    }
                })
            });

        let fixed_edges_iter = instance
            .fixed_edge
            .iter()
            .filter(|m_edge| {
                let i = path.index_of_super_node(m_edge.0);
                let j = path.index_of_super_node(m_edge.1);
                i.max(j) - i.min(j) >= 2
            })
            .flat_map(move |cycle_edge| {
                let i = path.index_of_super_node(cycle_edge.0);
                let j = path.index_of_super_node(cycle_edge.1);

                let mut pseudo_nodes = self.input.path.nodes.as_slice()[i..=j].to_vec();

                pseudo_nodes.last_mut().unwrap().get_zoomed_mut().out_node = Some(cycle_edge.1);
                pseudo_nodes.first_mut().unwrap().get_zoomed_mut().in_node = Some(cycle_edge.0);

                let mut path_iter: Box<dyn Iterator<Item = Vec<SuperNode>>> =
                    Box::new(vec![pseudo_nodes].into_iter());
                for (k, l) in (i..=j).tuple_windows() {
                    path_iter = Box::new(path_iter.into_iter().flat_map(move |nodes| {
                        let pk = k - i;
                        let pl = l - i;
                        let nodes_clone = nodes.clone();

                        instance
                            .fixed_edges_between(k, l)
                            .into_iter()
                            .map(move |path_edge| {
                                let mut nodes = nodes.clone();
                                nodes[pk].get_zoomed_mut().out_node = Some(path_edge.0);
                                nodes[pl].get_zoomed_mut().in_node = Some(path_edge.1);
                                nodes
                            })
                            .chain(vec![nodes_clone].into_iter())
                    }));
                }

                path_iter.map(|nodes| {
                    let cycle = PseudoCycle { nodes };

                    PseudoCycleInstance {
                        path_matching: self.input.clone(),
                        cycle_edge: CycleEdge::Fixed(cycle_edge.clone()),
                        pseudo_cycle: cycle,
                    }
                })
            });

        Box::new(matching_edges_iter.chain(fixed_edges_iter))
    }
}

impl EnumeratorTactic<AugmentedPathInstance, PseudoCycleInstance, PathContext>
    for PseudoCyclesEnum
{
    type Enumer<'a> = PseudoCyclesEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &AugmentedPathInstance) -> String {
        format!("Enumerate all pseudo cycles")
    }

    fn item_msg(&self, item: &PseudoCycleInstance) -> String {
        format!("Pseudo cycle via cycle edge {}", item.cycle_edge)
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
        format!("Pseudo cycle via cycle edge {}", item.cycle_edge)
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        PseudoCyclesEnumerator {
            input: &data.instance,
        }
    }
}
