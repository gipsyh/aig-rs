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

    pub fn coi(&self, root: &[usize]) -> HashSet<usize> {
        let mut latchs = HashMap::new();
        for l in self.latchs.iter() {
            latchs.insert(l.input, *l);
        }
        let mut refine = HashSet::new();
        refine.insert(AigEdge::constant_edge(true).node_id());
        let mut queue = Vec::new();
        for r in root {
            if !refine.contains(r) {
                queue.push(*r);
                refine.insert(*r);
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
        refine
    }

    pub fn coi_refine(&self) -> (Aig, HashMap<usize, usize>) {
        let aig_bad = if self.bads.is_empty() {
            self.outputs[0]
        } else {
            self.bads[0]
        };
        let mut refine_root: Vec<usize> = self.constraints.iter().map(|c| c.node_id()).collect();
        refine_root.push(aig_bad.node_id());
        let refine = self.coi(&refine_root);
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
        let mut remap = HashMap::new();
        for n in self.nodes.iter() {
            if let Some(new_id) = refine_map.get(&n.node_id()) {
                remap.insert(*new_id, n.node_id());
                let mut new_node = n.clone();
                new_node.id = *new_id;
                if let AigNodeType::And(fanin0, fanin1) = &mut new_node.typ {
                    *fanin0 = edge_map(*fanin0).unwrap();
                    *fanin1 = edge_map(*fanin1).unwrap();
                }
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
        let mut latch_group = HashMap::new();
        for (l, g) in self.latch_group.iter() {
            if let Some(newl) = refine_map.get(l) {
                latch_group.insert(*newl, *g);
            }
        }
        (
            Self {
                nodes,
                inputs,
                latchs,
                outputs,
                bads,
                constraints,
                latch_group,
            },
            remap,
        )
    }

    // pub fn constraint_to_latch(&mut self) {
    //     let constraints = take(&mut self.constraints);
    //     let num_origin_latchs = self.latchs.len();
    //     for c in constraints {
    //         if c == AigEdge::constant_edge(true) {
    //             continue;
    //         }
    //         let input = self.new_input_node();
    //         let next = self.new_and_node(c, input.into());
    //         self.new_latch(input, next, Some(true));
    //     }
    //     if self.latchs.len() > num_origin_latchs {
    //         let mut c = self.latchs[num_origin_latchs].next;
    //         for i in num_origin_latchs + 1..self.latchs.len() {
    //             c = self.new_and_node(c, self.latchs[i].next);
    //         }
    //         if self.bads.is_empty() {
    //             self.outputs[0] = self.new_and_node(self.outputs[0], c);
    //         } else {
    //             self.bads[0] = self.new_and_node(self.bads[0], c);
    //         };
    //     }
    // }

    // pub fn unroll(&self) -> Aig {
    //     let mut next_map = HashMap::new();
    //     let false_edge = AigEdge::constant_edge(false);
    //     next_map.insert(false_edge.node_id(), false_edge);
    //     for l in self.latchs.iter() {
    //         next_map.insert(l.input, l.next);
    //     }
    //     let mut ans = self.clone();
    //     for i in self.nodes_range() {
    //         if next_map.contains_key(&i) {
    //             continue;
    //         }
    //         if self.nodes[i].is_and() {
    //             let fanin0 = self.nodes[i].fanin0();
    //             let fanin1 = self.nodes[i].fanin1();
    //             let fanin0 = next_map[&fanin0.node_id()].not_if(fanin0.compl());
    //             let fanin1 = next_map[&fanin1.node_id()].not_if(fanin1.compl());
    //             let next = ans.new_and_node(fanin0, fanin1);
    //             next_map.insert(i, next);
    //         } else {
    //             let input = ans.new_input_node();
    //             ans.inputs.push(input);
    //             let next: AigEdge = input.into();
    //             next_map.insert(i, next);
    //         }
    //     }
    //     for l in ans.latchs.iter_mut() {
    //         l.next = next_map[&l.next.node_id()].not_if(l.next.compl());
    //     }
    //     for o in ans.outputs.iter_mut() {
    //         *o = next_map[&o.node_id()].not_if(o.compl());
    //     }
    //     for b in ans.bads.iter_mut() {
    //         *b = next_map[&b.node_id()].not_if(b.compl());
    //     }
    //     for c in 0..ans.constraints.len() {
    //         let next = next_map[&ans.constraints[c].node_id()].not_if(ans.constraints[c].compl());
    //         ans.constraints.push(next)
    //     }
    //     assert!(ans.inputs.len() == self.inputs.len() * 2);
    //     assert!(ans.latchs.len() == self.latchs.len());
    //     assert!(ans.outputs.len() == self.outputs.len());
    //     assert!(ans.bads.len() == self.bads.len());
    //     assert!(ans.constraints.len() == self.constraints.len() * 2);
    //     ans
    // }
}
