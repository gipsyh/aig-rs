use crate::{Aig, AigEdge, AigLatch, AigNode};
use std::{io, path::Path};

impl Aig {
    fn setup_levels(&mut self) {
        let mut levels = vec![0; self.num_nodes()];
        for and in self.ands_iter() {
            let fanin0 = and.fanin0().node_id();
            let fanin1 = and.fanin1().node_id();
            levels[and.node_id()] = levels[fanin0].max(levels[fanin1]) + 1;
        }
        for (id, node) in levels.iter().enumerate() {
            self.nodes[id].level = *node;
        }
    }

    fn setup_fanouts(&mut self) {
        for id in self.nodes_range() {
            if self.nodes[id].is_and() {
                let fanin0 = self.nodes[id].fanin0();
                let compl = fanin0.compl();
                self.nodes[fanin0.node_id()]
                    .fanouts
                    .push(AigEdge::new(id, compl));
                let fanin1 = self.nodes[id].fanin1();
                let compl = fanin1.compl();
                self.nodes[fanin1.node_id()]
                    .fanouts
                    .push(AigEdge::new(id, compl));
            }
        }
    }

    pub fn from_file<P: AsRef<Path>>(file: P) -> io::Result<Self> {
        let file = std::fs::File::open(file)?;
        let aiger = aiger::Reader::from_reader(file).unwrap();
        let header = aiger.header();
        let mut nodes: Vec<AigNode> = Vec::with_capacity(header.i + header.l + header.a + 1);
        let nodes_remaining = nodes.spare_capacity_mut();
        nodes_remaining[0].write(AigNode::new_false(0));
        let mut inputs = Vec::new();
        let mut latchs = Vec::new();
        let mut outputs = Vec::new();
        let mut bads = Vec::new();
        let mut constraints = Vec::new();
        for obj in aiger.records() {
            let obj = obj.unwrap();
            match obj {
                aiger::Aiger::Input(input) => {
                    let id = input.0 / 2;
                    nodes_remaining[id].write(AigNode::new_prime_input(id));
                    inputs.push(id);
                }
                aiger::Aiger::Latch {
                    output,
                    input,
                    init,
                } => {
                    let id = output.0 / 2;
                    nodes_remaining[id].write(AigNode::new_latch_input(id));
                    latchs.push(AigLatch::new(
                        id,
                        AigEdge::new(input.0 / 2, input.0 & 0x1 != 0),
                        init,
                    ));
                }
                aiger::Aiger::Output(o) => outputs.push(AigEdge::new(o.0 / 2, o.0 & 0x1 != 0)),
                aiger::Aiger::BadState(b) => bads.push(AigEdge::new(b.0 / 2, b.0 & 0x1 != 0)),
                aiger::Aiger::Constraint(c) => {
                    constraints.push(AigEdge::new(c.0 / 2, c.0 & 0x1 != 0))
                }
                aiger::Aiger::AndGate { output, inputs } => {
                    let id = output.0 / 2;
                    nodes_remaining[id].write(AigNode::new_and(
                        id,
                        AigEdge::new(inputs[0].0 / 2, inputs[0].0 & 0x1 != 0),
                        AigEdge::new(inputs[1].0 / 2, inputs[1].0 & 0x1 != 0),
                        0,
                    ));
                }
                aiger::Aiger::Symbol {
                    type_spec: _,
                    position: _,
                    symbol: _,
                } => (),
            }
        }
        unsafe { nodes.set_len(header.i + header.l + header.a + 1) };
        let mut ret = Self {
            nodes,
            inputs,
            latchs,
            outputs,
            bads,
            constraints,
        };
        ret.setup_levels();
        ret.setup_fanouts();
        Ok(ret)
    }
}
