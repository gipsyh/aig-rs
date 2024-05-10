use crate::{Aig, AigCube, AigEdge, AigNodeType};
use std::collections::{HashMap, HashSet};

impl Aig {
    pub fn latch_init_cube(&self) -> AigCube {
        AigCube::from_iter(
            self.latchs
                .iter()
                .filter_map(|l| l.init.map(|init| AigEdge::new(l.input, !init))),
        )
    }

    pub fn coi_refine(&self, root: &[AigEdge]) -> Aig {
        let mut latchs = HashMap::new();
        for l in self.latchs.iter() {
            latchs.insert(l.input, *l);
        }
        let mut refine = HashSet::new();
        refine.insert(AigEdge::constant_edge(true).node_id());
        let mut queue = Vec::new();
        for r in root {
            if !refine.contains(&r.node_id()) {
                queue.push(r.node_id());
                refine.insert(r.node_id());
            }
        }
        while let Some(n) = queue.pop() {
            let mut refine_insert = |n: usize| {
                if !refine.contains(&n) {
                    queue.push(n);
                    refine.insert(n);
                }
            };
            if self.nodes[n].is_and() {
                let fanin0 = self.nodes[n].fanin0();
                let fanin1 = self.nodes[n].fanin1();
                refine_insert(fanin0.node_id());
                refine_insert(fanin1.node_id());
            } else if let Some(l) = latchs.get(&n) {
                refine_insert(l.next.node_id());
            }
        }
        let mut refine = Vec::from_iter(refine);
        refine.sort();
        let mut refine_map = HashMap::new();
        for (i, r) in refine.iter().enumerate() {
            refine_map.insert(r, i);
        }
        let edge_map = |e: AigEdge| {
            refine_map
                .get(&e.id)
                .map(|new_id| AigEdge::new(*new_id, e.complement))
        };
        let mut nodes = Vec::new();
        for n in self.nodes.iter() {
            if let Some(new_id) = refine_map.get(&n.node_id()) {
                let mut new_node = n.clone();
                new_node.id = *new_id;
                if let AigNodeType::And(fanin0, fanin1) = &mut new_node.typ {
                    *fanin0 = edge_map(*fanin0).unwrap();
                    *fanin1 = edge_map(*fanin1).unwrap();
                }
                new_node.fanouts = new_node
                    .fanouts
                    .iter()
                    .filter_map(|n| edge_map(*n))
                    .collect();
                nodes.push(new_node);
            }
        }
        let inputs: Vec<usize> = self
            .inputs
            .iter()
            .filter_map(|n| refine_map.get(n).cloned())
            .collect();
        let mut latchs = Vec::new();
        for l in self.latchs.iter() {
            if let Some(new_input) = refine_map.get(&l.input) {
                let mut new_latch = *l;
                new_latch.input = *new_input;
                new_latch.next = edge_map(new_latch.next).unwrap();
                latchs.push(new_latch);
            }
        }
        let outputs: Vec<AigEdge> = self.outputs.iter().filter_map(|n| edge_map(*n)).collect();
        let bads: Vec<AigEdge> = self.bads.iter().filter_map(|n| edge_map(*n)).collect();
        let constraints: Vec<AigEdge> = self
            .constraints
            .iter()
            .filter_map(|n| edge_map(*n))
            .collect();
        Self {
            nodes,
            inputs,
            latchs,
            outputs,
            bads,
            constraints,
        }
    }
}
