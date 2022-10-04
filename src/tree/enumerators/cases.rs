use crate::{
    proof_logic::{Enumerator, EnumeratorTactic},
    tree::{TreeCaseInstance, TreeContext},
    util::relabels_nodes_sequentially,
};

pub struct CompEnum;

pub struct CasesEnumerator<'a> {
    input: &'a TreeCaseInstance,
}

impl<'a> Enumerator<TreeCaseInstance, TreeContext> for CasesEnumerator<'a> {
    fn iter(&self, context: &TreeContext) -> Box<dyn Iterator<Item = TreeCaseInstance> + '_> {
        let iter = context.inner_comps.clone().into_iter().map(|c| {
            let mut comps = self.input.comps.clone();
            comps.push(c);
            let edges = self.input.edges.clone();
            relabels_nodes_sequentially(&mut comps);
            TreeCaseInstance { comps, edges }
        });
        Box::new(iter)
    }
}

impl EnumeratorTactic<TreeCaseInstance, TreeCaseInstance, TreeContext> for CompEnum {
    type Enumer<'a> = CasesEnumerator<'a>;

    fn msg(&self, _data_in: &TreeCaseInstance) -> String {
        format!("Enumerate more components")
    }

    fn get_enumerator<'a>(&'a self, data: &'a TreeCaseInstance) -> Self::Enumer<'a> {
        CasesEnumerator { input: data }
    }

    fn item_msg(&self, item: &TreeCaseInstance) -> String {
        format!("{}", item)
    }
}
