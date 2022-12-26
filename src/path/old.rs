

impl Display for ZoomedNode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[ {}: ", self.comp.short_name())?;
        if let Some(n) = self.in_node {
            write!(f, "in={}, ", n)?;
        }
        if let Some(n) = self.out_node {
            write!(f, "out={}, ", n)?;
        }
        write!(f, "used={} ]", self.used)
    }
}

#[derive(Clone, Debug)]
pub struct SelectedHitInstance {
    pub instance: AugmentedPathInstance,
    pub hit_comp_idx: Pidx,
    pub last_hit: bool,
}

#[derive(Clone, Debug)]
pub struct PseudoCycleInstance {
    pub instance: AugmentedPathInstance,
    pub pseudo_cycle: PseudoCycle,
}

#[derive(Clone, Debug)]
pub struct PathRearrangementInstance {
    pub instance: AugmentedPathInstance,
    pub start_idx: Pidx,
    pub extension: Vec<SuperNode>,
}

#[derive(Clone, Debug)]
pub enum CycleEdge {
    Fixed,
    Matching(AbstractEdge),
}

impl Display for CycleEdge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            CycleEdge::Fixed => write!(f, "Fixed edges"),
            CycleEdge::Matching(e) => write!(f, "{}", e),
        }
    }
}

#[derive(Clone, Debug)]
pub struct PseudoCycle {
    nodes: Vec<SuperNode>,
}

impl PseudoCycle {
    /// checks whether this cycle includes all components of a suffix
    pub fn consecutive_end(&self) -> bool {
        let mut indices = self.nodes.iter().map(|n| n.path_idx().raw()).collect_vec();
        indices.sort();
        indices.contains(&0) && *indices.last().unwrap() == indices.len() - 1
    }
}



#[derive(Clone, Debug)]
pub struct AugmentedPathInstance {
    nodes: Vec<SuperNode>,
    pub abstract_edges: Vec<AbstractEdge>,
    pub fixed_edges: Vec<Edge>,
}

impl AugmentedPathInstance {
    pub fn index_of_super_node(&self, node: Node) -> Pidx {
        let raw = self
            .nodes
            .iter()
            .enumerate()
            .find(|(_i, super_node)| super_node.get_comp().contains(&node))
            .unwrap()
            .0;

        Pidx::from(raw)
    }

    pub fn path_len(&self) -> usize {
        self.nodes.len()
    }

    pub fn all_outside_hits(&self) -> Vec<AbstractEdge> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_outside())
            .cloned()
            .collect_vec()
    }

    pub fn outside_hits_from(&self, path_idx: Pidx) -> Vec<AbstractEdge> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_outside() && e.source_path() == path_idx)
            .cloned()
            .collect_vec()
    }

    pub fn outside_edges_on(&self, path_idx: Pidx) -> Vec<Node> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_outside() && e.source_path() == path_idx)
            .map(|e| e.source())
            .collect_vec()
    }

    // Returns a list of nodes of path_idx which can have _one_ additional matching edge
    pub fn unmatched_nodes(&self, path_idx: Pidx) -> Vec<Node> {
        let comp = self[path_idx].get_comp();

        if let Component::Large(n) = comp {
            return vec![*n];
        }
        let fixed_incident = self.fixed_incident_edges(path_idx);
        let matching_sources = self.nodes_with_abstract_edges(path_idx);

        comp.matching_nodes()
            .into_iter()
            .filter(|n| {
                !(matching_sources.contains(n)
                    || fixed_incident.iter().any(|e| {
                        e.node_incident(n)
                            && !fixed_incident
                                .iter()
                                .any(|e2| !e2.node_incident(n) && e.edge_incident(e2))
                    }))
            })
            .cloned()
            .collect_vec()
    }

    pub fn nodes_with_fixed_edges(&self, path_idx: Pidx) -> Vec<Node> {
        let mut edge_endpoints = self
            .fixed_edges
            .iter()
            .flat_map(|e| e.endpoint_at(path_idx))
            .collect_vec();

        if let SuperNode::Zoomed(zoomed) = &self[path_idx] {
            if let Some(node) = zoomed.in_node {
                assert!(self[path_idx].get_comp().contains(&node));
                edge_endpoints.push(node)
            }
            if let Some(node) = zoomed.out_node {
                assert!(self[path_idx].get_comp().contains(&node));
                edge_endpoints.push(node)
            }
        }
        assert!(edge_endpoints
            .iter()
            .all(|n| self[path_idx].get_comp().contains(n)));
        edge_endpoints
    }

    pub fn nodes_with_abstract_edges(&self, path_idx: Pidx) -> Vec<Node> {
        let endpoints = self
            .abstract_edges
            .iter()
            .filter(|e| e.source_path() == path_idx)
            .map(|e| e.source())
            .collect_vec();

        assert!(endpoints
            .iter()
            .all(|n| self[path_idx].get_comp().contains(n)));
        endpoints
    }

    pub fn nodes_with_edges(&self, path_idx: Pidx) -> Vec<Node> {
        vec![
            self.nodes_with_abstract_edges(path_idx),
            self.nodes_with_fixed_edges(path_idx),
        ]
        .into_iter()
        .flatten()
        .unique()
        .collect_vec()
    }

    pub fn nodes_without_edges(&self, path_idx: Pidx) -> Vec<Node> {
        let edge_endpoints = self.nodes_with_edges(path_idx);

        self[path_idx]
            .get_comp()
            .graph()
            .nodes()
            .filter(|n| !edge_endpoints.contains(n))
            .collect_vec()
    }

    pub fn matching_edges_hit(&self, path_idx: Pidx) -> Vec<AbstractEdge> {
        self.abstract_edges
            .iter()
            .filter(|e| e.hits_path() == Some(path_idx))
            .cloned()
            .collect_vec()
    }

    pub fn fix_matching_edge(
        &mut self,
        matching_edge: &AbstractEdge,
        hit_idx: Pidx,
        new_target: Node,
    ) {
        self.abstract_edges.drain_filter(|e| matching_edge == e);

        self.fixed_edges.push(Edge::new(
            new_target,
            hit_idx,
            matching_edge.source(),
            matching_edge.source_path(),
        ));
    }

    /// Returns fixed edges incident on `idx`
    pub fn fixed_incident_edges(&self, idx: Pidx) -> Vec<Edge> {
        self.fixed_edges
            .iter()
            .filter(|e| e.path_incident(idx))
            .cloned()
            .chain(
                vec![
                    self.path_edge(idx),
                    idx.succ().and_then(|left| self.path_edge(left)),
                ]
                .into_iter()
                .flatten(),
            )
            .collect_vec()
    }

    /// Returns path edge between `idx` and `idx + 1`
    fn path_edge(&self, idx: Pidx) -> Option<Edge> {
        if idx.raw() >= self.nodes.len() {
            return None;
        }
        if self[idx].is_zoomed() && self[idx.prec()].is_zoomed() {
            Some(Edge::new(
                self[idx.prec()].get_zoomed().out_node.unwrap(),
                idx.prec(),
                self[idx].get_zoomed().in_node.unwrap(),
                idx,
            ))
        } else {
            None
        }
    }

    pub fn all_fixed_edges(&self) -> Vec<Edge> {
        let mut edges = self
            .fixed_edges.clone();
            
        for node in self.nodes.iter().take(self.nodes.len() - 1) {
            if let Some(path_edge) = self.path_edge(node.path_idx()) {
                edges.push(path_edge);
            }
        }
        edges
    }

    pub fn abstract_edges_between(&self, idx1: Pidx, idx2: Pidx) -> Vec<AbstractEdge> {
         self
            .abstract_edges
            .iter()
            .filter(|&edge| edge.between_path_nodes(idx1, idx2))
            .cloned()
            .collect_vec()
    }

    pub fn fixed_edges_between(&self, idx1: Pidx, idx2: Pidx) -> Vec<Edge> {
        let mut edges = self
            .fixed_edges
            .iter()
            .filter(|&edge| edge.between_path_nodes(idx1, idx2))
            .cloned()
            .collect_vec();

        if idx1.dist(&idx2) == 1 {
            if let Some(path_edge) = self.path_edge(idx1.min(idx2)) {
                edges.push(path_edge);
            }
        }

        edges
    }
}

impl Index<Pidx> for AugmentedPathInstance {
    type Output = SuperNode;

    fn index(&self, index: Pidx) -> &Self::Output {
        &self.nodes[index.raw()]
    }
}

impl IndexMut<Pidx> for AugmentedPathInstance {
    fn index_mut(&mut self, index: Pidx) -> &mut Self::Output {
        &mut self.nodes[index.raw()]
    }
}

impl Display for AugmentedPathInstance {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[")?;
        write!(
            f,
            "{}",
            self.nodes
                .iter()
                .map(|node| format!("{}", node))
                .join(" -- ")
        )?;
        write!(f, "]")
    }
}
