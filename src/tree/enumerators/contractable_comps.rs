use itertools::Itertools;

use crate::{
    proof_logic::{Enumerator, EnumeratorTactic},
    tree::{utils::get_merge_graph, ContractableCompInstance, TreeCaseInstance, TreeContext},
};

pub struct ContractableCompsEnum {
    last_is_leaf: bool
}

impl ContractableCompsEnum {
    pub fn new(last_is_leaf: bool) -> Self {
        Self { last_is_leaf }
    }
}

pub struct ContractableCompsEnumerator<'a> {
    instance: &'a TreeCaseInstance,
    last_is_leaf: bool,
}

impl<'a> Enumerator<ContractableCompInstance, TreeContext> for ContractableCompsEnumerator<'a> {
    fn iter(
        &self,
        _context: &TreeContext,
    ) -> Box<dyn Iterator<Item = ContractableCompInstance> + '_> {
        let graph = get_merge_graph(&self.instance.comps, &self.instance.edges);
        let take = if self.last_is_leaf { self.instance.comps.len() } else { self.instance.comps.len() - 1 };

        let iter = self
            .instance
            .comps
            .iter()
            .enumerate()
            .take(take)
            .filter(|(_, c)| c.is_c6() || c.is_c5())
            .flat_map(move |(idx, comp)| {
                let comp_graph = comp.graph();
                // comp is H
                let mut necessary_edges = 0;
                let mut inner_vertices = vec![];
                for v in comp_graph.nodes() {
                    if graph.neighbors(v).all(|u| comp_graph.contains_node(u)) {
                        // v has only neighbors in H, i.e. no incident matching edges
                        inner_vertices.push(v);
                        necessary_edges += 2;
                    }
                }

                for edge in inner_vertices.iter().combinations(2) {
                    let u = edge[0];
                    let v = edge[1];

                    if graph.contains_edge(*u, *v) {
                        necessary_edges -= 1;
                    }
                }

                if 5 * necessary_edges >= 4 * comp.num_edges() {
                    Some(ContractableCompInstance {
                        instance: self.instance.clone(),
                        contr_idx: idx,
                        free_nodes: inner_vertices,
                    })
                } else {
                    None
                }
            });

        Box::new(iter)
    }
}

impl EnumeratorTactic<TreeCaseInstance, ContractableCompInstance, TreeContext>
    for ContractableCompsEnum
{
    type Enumer<'a> = ContractableCompsEnumerator<'a>;

    fn msg(&self, _data_in: &TreeCaseInstance) -> String {
        format!("Enumerate more components")
    }

    fn get_enumerator<'a>(&'a self, data: &'a TreeCaseInstance) -> Self::Enumer<'a> {
        ContractableCompsEnumerator { instance: data, last_is_leaf: self.last_is_leaf }
    }

    fn item_msg(&self, item: &ContractableCompInstance) -> String {
        format!(
            "Component {} contractible! Free nodes [{}]",
            item.contr_idx,
            item.free_nodes.iter().join(",")
        )
    }

    fn precondition(&self, data: &TreeCaseInstance, _context: &TreeContext) -> bool {
        let take = if self.last_is_leaf { data.comps.len() } else { data.comps.len() - 1 };
            
            data.comps
            .iter()
            .take(take)
            .any(|c| c.is_c6() || c.is_c5())
        
        
    }
}
