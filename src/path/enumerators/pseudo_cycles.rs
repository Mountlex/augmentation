use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    CycleEdgeInstance, PseudoCycle, PseudoCycleInstance, 
};

pub struct PseudoCyclesEnumTactic {
    worst_case: bool,
}

impl PseudoCyclesEnumTactic {
    pub fn new(worst_case: bool) -> Self {
        Self { worst_case }
    }
}

pub struct PseudoCyclesEnumerator<'a> {
    input: &'a CycleEdgeInstance,
    worst_case: bool,
}

impl<'a> Enumerator<CycleEdgeInstance, PseudoCycleInstance> for PseudoCyclesEnumerator<'a> {
    fn iter(
        &mut self,
        _context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = PseudoCycleInstance> + '_> {
        let cases = if self.worst_case {
            vec![false]
        } else {
            vec![true, false]
        };

        let iter = cases.into_iter().map(|np| {
            let cycle_edge = self.input.cycle_edge;
            let mut pseudo_nodes = self
                .input
                .path_matching
                .path
                .nodes
                .split_at(cycle_edge.hits_path().unwrap())
                .1
                .to_vec();

            pseudo_nodes.last_mut().unwrap().get_zoomed_mut().out_node = Some(cycle_edge.source());
            pseudo_nodes
                .first_mut()
                .unwrap()
                .get_abstract_mut()
                .nice_pair = np;

            let cycle = PseudoCycle {
                nodes: pseudo_nodes,
            };
            PseudoCycleInstance {
                path_matching: self.input.path_matching.clone(),
                cycle_edge: self.input.cycle_edge.clone(),
                pseudo_cycle: cycle,
            }
        });

        Box::new(iter)
    }
}

impl EnumeratorTactic<CycleEdgeInstance, PseudoCycleInstance> for PseudoCyclesEnumTactic {
    type Enumer<'a> = PseudoCyclesEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &CycleEdgeInstance) -> String {
        format!("Enumerate all pseudo cycles")
    }

    fn item_msg(&self, item: &PseudoCycleInstance) -> String {
        format!("Pseudo cycle {}", item.pseudo_cycle)
    }

    fn get_enumerator<'a>(&'a self, data: &'a CycleEdgeInstance) -> Self::Enumer<'a> {
        PseudoCyclesEnumerator {
            input: data,
            worst_case: self.worst_case,
        }
    }
}
