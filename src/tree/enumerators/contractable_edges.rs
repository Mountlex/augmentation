use itertools::Itertools;

use crate::{
    proof_logic::{Enumerator, EnumeratorTactic},
    tree::{ContractableCompInstance, TreeCaseInstance, TreeContext},
    types::Edge,
};

pub struct ContractableEdgesEnum;

pub struct ContractableEdgesEnumerator<'a> {
    instance: &'a ContractableCompInstance,
}

impl<'a> Enumerator<TreeCaseInstance, TreeContext> for ContractableEdgesEnumerator<'a> {
    fn iter(&self, _context: &TreeContext) -> Box<dyn Iterator<Item = TreeCaseInstance> + '_> {
        let comp = &self.instance.instance.comps[self.instance.contr_idx];

        let iter = self
            .instance
            .free_nodes
            .iter()
            .combinations(2)
            .filter(|e| !comp.is_adjacent(e[0], e[1]))
            .map(|e| {
                let mut instance_clone = self.instance.instance.clone();
                let new_edge = Edge::from_tuple(*e[0], *e[1]);
                instance_clone.edges.push(new_edge);
                instance_clone
            });

        Box::new(iter)
    }
}

impl EnumeratorTactic<ContractableCompInstance, TreeCaseInstance, TreeContext>
    for ContractableEdgesEnum
{
    type Enumer<'a> = ContractableEdgesEnumerator<'a>;

    fn msg(&self, _data_in: &ContractableCompInstance) -> String {
        String::new()
    }

    fn get_enumerator<'a>(&'a self, data: &'a ContractableCompInstance) -> Self::Enumer<'a> {
        ContractableEdgesEnumerator { instance: data }
    }

    fn item_msg(&self, item: &TreeCaseInstance) -> String {
        format!(
            "Contractability implied edge: Edges [{}]",
            item.edges.iter().join(", ")
        )
    }
}
