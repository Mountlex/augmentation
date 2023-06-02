use super::instance::{Instance, StackElement};
use crate::logic::{EnumeratorTrait, InstanceTrait, OptEnumeratorTrait};

mod edges;
mod path_nodes;
mod pseudo_cycles;
mod rearrangements;

pub use path_nodes::path_comp_enumerator;

#[derive(Clone, Debug)]
pub enum Enumerator {
    //NicePairs,
    PseudoCycle(bool),
    Rearrangments(bool),
}

impl EnumeratorTrait for Enumerator {
    type Inst = Instance;

    fn msg(&self) -> &str {
        match self {
            //Enumerator::PathNodes => "Enumerate new path node",
            //Enumerator::NicePairs => "Enumerate nice pairs",
            Enumerator::PseudoCycle(_) => "Enumerate pseudo cycles",
            Enumerator::Rearrangments(_) => "Enumerate rearrangements",
        }
    }

    fn get_iter(
        &self,
        stack: &Instance,
    ) -> Box<dyn Iterator<Item = <Instance as InstanceTrait>::StackElement>> {
        match self {
            // Enumerator::PathNodes => {
            //     Box::new(path_extension_enumerator(stack).map(StackElement::Inst))
            // }
            //Enumerator::NicePairs => Box::new(nice_pairs_enumerator(stack).map(StackElement::Inst)),
            Enumerator::PseudoCycle(finite) => Box::new(
                pseudo_cycles::enumerate_pseudo_cycles(stack, *finite)
                    .map(StackElement::PseudoCycle),
            ),

            Enumerator::Rearrangments(finite) => Box::new(
                rearrangements::enumerate_rearrangements(stack, *finite)
                    .map(StackElement::Rearrangement),
            ),
        }
    }
}

#[derive(Debug, Clone)]
pub enum OptEnumerator {
    Edges(bool),
    PathNode,
}

impl OptEnumeratorTrait for OptEnumerator {
    type Inst = Instance;

    fn msg(&self) -> &str {
        match self {
            OptEnumerator::Edges(_) => "Enumerate edges",
            OptEnumerator::PathNode => "Enumerate path node",
        }
    }

    fn try_iter(
        &self,
        instance: &mut Instance,
    ) -> Option<(Box<dyn Iterator<Item = StackElement>>, String)> {
        let result = match self {
            OptEnumerator::Edges(finite) => edges::edge_enumerator(instance, *finite),
            OptEnumerator::PathNode => path_nodes::path_extension_enumerator(instance),
        };

        if let Some((case_iter, msg)) = result {
            Some((Box::new(case_iter.map(StackElement::Inst)), msg))
        } else {
            None
        }
    }
}
