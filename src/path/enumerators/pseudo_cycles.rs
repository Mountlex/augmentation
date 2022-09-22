use crate::{
    path::{
        proof::{Enumerator, EnumeratorTactic, ProofContext},
        AugmentedPathInstance, CycleEdge, MatchingEdge, PathHit, PseudoCycle, PseudoCycleInstance,
        SelectedHitInstance,
    },
    types::Edge,
};

pub struct PseudoCyclesEnumTactic;

pub struct PseudoCyclesEnumerator<'a> {
    input: &'a AugmentedPathInstance,
}

impl<'a> Enumerator<PseudoCycleInstance> for PseudoCyclesEnumerator<'a> {
    fn iter(
        &mut self,
        context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = PseudoCycleInstance> + '_> {
        let path_len = context.path_len;
        let matching_edges_iter = self
            .input
            .non_path_matching_edges
            .iter()
            .filter(move |m_edge| matches!(m_edge.hit(), PathHit::Path(r) if r <= path_len - 3))
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
            .filter(|m_edge| {
                self.input.path.index_of_super_node(m_edge.0) <= 1
                    && self.input.path.index_of_super_node(m_edge.1) == 3
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

impl EnumeratorTactic<AugmentedPathInstance, PseudoCycleInstance> for PseudoCyclesEnumTactic {
    type Enumer<'a> = PseudoCyclesEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &AugmentedPathInstance) -> String {
        format!("Enumerate all pseudo cycles")
    }

    fn item_msg(&self, item: &PseudoCycleInstance) -> String {
        format!("Pseudo cycle {}", item.pseudo_cycle)
    }

    fn get_enumerator<'a>(&'a self, data: &'a AugmentedPathInstance) -> Self::Enumer<'a> {
        PseudoCyclesEnumerator { input: data }
    }
}

impl EnumeratorTactic<SelectedHitInstance, PseudoCycleInstance> for PseudoCyclesEnumTactic {
    type Enumer<'a> = PseudoCyclesEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &SelectedHitInstance) -> String {
        format!("Enumerate all pseudo cycles")
    }

    fn item_msg(&self, item: &PseudoCycleInstance) -> String {
        format!("Pseudo cycle {}", item.pseudo_cycle)
    }

    fn get_enumerator<'a>(&'a self, data: &'a SelectedHitInstance) -> Self::Enumer<'a> {
        PseudoCyclesEnumerator {
            input: &data.instance,
        }
    }
}
