use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    AugmentedPathInstance, CycleEdge, PathHit, PseudoCycle, PseudoCycleInstance,
    SelectedHitInstance,
};

#[derive(Clone)]
pub struct PseudoCyclesEnum;

pub struct PseudoCyclesEnumerator<'a> {
    input: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<PseudoCycleInstance> for PseudoCyclesEnumerator<'a> {
    fn iter(
        &mut self,
        context: &ProofContext,
    ) -> Box<dyn Iterator<Item = PseudoCycleInstance> + '_> {
        let path_len = context.path_len;
        let path = &self.input.path;

        let matching_edges_iter = self
            .input
            .non_path_matching_edges
            .iter()
            .filter(move |m_edge| {
                if let Some(i) = m_edge.hits_path() {
                    let k = path.index_of_super_node(m_edge.source());
                    i.max(k) - i.min(k) >= 2
                } else {
                    false
                }
            })
            .map(|cycle_edge| {
                let mut pseudo_nodes = self
                    .input
                    .path
                    .nodes
                    .split_at(cycle_edge.hits_path().unwrap())
                    .1
                    .to_vec();

                pseudo_nodes.last_mut().unwrap().get_zoomed_mut().out_node =
                    Some(cycle_edge.source());
                pseudo_nodes
                    .first_mut()
                    .unwrap()
                    .get_abstract_mut()
                    .nice_pair = false;

                let cycle = PseudoCycle {
                    nodes: pseudo_nodes,
                };

                PseudoCycleInstance {
                    path_matching: self.input.clone(),
                    cycle_edge: CycleEdge::Matching(cycle_edge.clone()),
                    pseudo_cycle: cycle,
                }
            });

        let fixed_edges_iter = self
            .input
            .fixed_edge
            .iter()
            .filter(move |m_edge| {
                let i = path.index_of_super_node(m_edge.0);
                let j = path.index_of_super_node(m_edge.1);
                i.max(j) - i.min(j) >= 2
            })
            .map(move |cycle_edge| {
                let mut pseudo_nodes = self
                    .input
                    .path
                    .nodes
                    .split_at(self.input.path.index_of_super_node(cycle_edge.0))
                    .1
                    .to_vec();

                pseudo_nodes.last_mut().unwrap().get_zoomed_mut().out_node = Some(cycle_edge.1);
                pseudo_nodes.first_mut().unwrap().get_zoomed_mut().in_node = Some(cycle_edge.0);

                let cycle = PseudoCycle {
                    nodes: pseudo_nodes,
                };

                PseudoCycleInstance {
                    path_matching: self.input.clone(),
                    cycle_edge: CycleEdge::Fixed(cycle_edge.clone()),
                    pseudo_cycle: cycle,
                }
            });

        Box::new(matching_edges_iter.chain(fixed_edges_iter))
    }
}

impl EnumeratorTactic<AugmentedPathInstance, PseudoCycleInstance> for PseudoCyclesEnum {
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

impl EnumeratorTactic<SelectedHitInstance, PseudoCycleInstance> for PseudoCyclesEnum {
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
