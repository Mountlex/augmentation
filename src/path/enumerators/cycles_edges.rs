use crate::path::{
    proof::{Enumerator, EnumeratorTactic, ProofContext},
    CycleEdgeInstance, PathHit, PathMatchingInstance,
};

pub struct CycleEdgeEnumTactic;

pub struct CycleEdgeEnumerator<'a> {
    input: &'a PathMatchingInstance,
}

impl<'a> Enumerator<PathMatchingInstance, CycleEdgeInstance> for CycleEdgeEnumerator<'a> {
    fn iter(
        &mut self,
        context: &mut ProofContext,
    ) -> Box<dyn Iterator<Item = CycleEdgeInstance> + '_> {
        let path_len = context.path_len;
        let iter = self
            .input
            .matching
            .other_edges
            .iter()
            .filter(move |m_edge| matches!(m_edge.hit(), PathHit::Path(r) if r <= path_len - 3))
            .map(|edge| CycleEdgeInstance {
                path_matching: self.input.clone(),
                cycle_edge: edge.clone(),
            });

        Box::new(iter)
    }
}

impl EnumeratorTactic<PathMatchingInstance, CycleEdgeInstance> for CycleEdgeEnumTactic {
    type Enumer<'a> = CycleEdgeEnumerator<'a> where Self: 'a;

    fn msg(&self, _data_in: &PathMatchingInstance) -> String {
        format!("Enumerate all pseudo cycles")
    }

    fn item_msg(&self, item: &CycleEdgeInstance) -> String {
        format!("Cycle formed by {}", item.cycle_edge)
    }

    fn get_enumerator<'a>(&'a self, data: &'a PathMatchingInstance) -> Self::Enumer<'a> {
        CycleEdgeEnumerator { input: data }
    }
}
