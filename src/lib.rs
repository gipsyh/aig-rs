mod aiger;
mod cnf;
mod display;
mod logic_form;
mod others;
mod ternary;

pub use ternary::*;

pub use crate::logic_form::*;
use ::logic_form::Lit;
use std::{
    cmp::Reverse,
    collections::BinaryHeap,
    mem::{swap, take},
    ops::{Index, Not, Range},
    vec,
};

pub type AigNodeId = usize;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct AigEdge {
    id: AigNodeId,
    complement: bool,
}

impl Not for AigEdge {
    type Output = AigEdge;

    fn not(mut self) -> Self::Output {
        self.complement = !self.complement;
        self
    }
}

impl From<AigNodeId> for AigEdge {
    fn from(value: AigNodeId) -> Self {
        Self {
            id: value,
            complement: false,
        }
    }
}

impl PartialOrd for AigEdge {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AigEdge {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.id.cmp(&other.id)
    }
}

impl AigEdge {
    pub fn new(id: AigNodeId, complement: bool) -> Self {
        Self { id, complement }
    }

    pub fn node_id(&self) -> AigNodeId {
        self.id
    }

    pub fn compl(&self) -> bool {
        self.complement
    }

    pub fn set_nodeid(&mut self, nodeid: AigNodeId) {
        self.id = nodeid;
    }

    pub fn set_compl(&mut self, compl: bool) {
        self.complement = compl
    }

    pub fn not_if(self, x: bool) -> Self {
        if x {
            !self
        } else {
            self
        }
    }

    pub fn constant_edge(polarity: bool) -> Self {
        AigEdge {
            id: 0,
            complement: polarity,
        }
    }

    pub fn from_lit(lit: Lit) -> Self {
        Self {
            id: lit.var().into(),
            complement: !lit.polarity(),
        }
    }

    pub fn to_lit(&self) -> Lit {
        Lit::new(self.id.into(), !self.complement)
    }
}

#[derive(Debug, Clone)]
pub struct AigLatch {
    pub input: AigNodeId,
    pub next: AigEdge,
    pub init: Option<bool>,
}

impl AigLatch {
    pub fn new(input: AigNodeId, next: AigEdge, init: Option<bool>) -> Self {
        Self { input, next, init }
    }
}

#[derive(Debug, Clone)]
pub enum AigNodeType {
    False,
    PrimeInput,
    LatchInput,
    And(AigEdge, AigEdge),
}

#[derive(Debug, Clone)]
pub struct AigNode {
    id: AigNodeId,
    level: usize,
    typ: AigNodeType,
    fanouts: Vec<AigEdge>,
}

impl AigNode {
    pub fn node_id(&self) -> AigNodeId {
        self.id
    }

    pub fn is_and(&self) -> bool {
        matches!(self.typ, AigNodeType::And(_, _))
    }

    pub fn is_prime_input(&self) -> bool {
        matches!(self.typ, AigNodeType::PrimeInput)
    }

    pub fn is_latch_input(&self) -> bool {
        matches!(self.typ, AigNodeType::LatchInput)
    }

    pub fn fanin0(&self) -> AigEdge {
        if let AigNodeType::And(ret, _) = self.typ {
            ret
        } else {
            panic!();
        }
    }

    pub fn fanin1(&self) -> AigEdge {
        if let AigNodeType::And(_, ret) = self.typ {
            ret
        } else {
            panic!();
        }
    }

    pub fn set_fanin0(&mut self, fanin: AigEdge) {
        if let AigNodeType::And(fanin0, _) = &mut self.typ {
            *fanin0 = fanin
        } else {
            panic!();
        }
    }

    pub fn set_fanin1(&mut self, fanin: AigEdge) {
        if let AigNodeType::And(_, fanin1) = &mut self.typ {
            *fanin1 = fanin
        } else {
            panic!();
        }
    }
}

impl AigNode {
    fn new_false(id: usize) -> Self {
        Self {
            id,
            typ: AigNodeType::False,
            fanouts: Vec::new(),
            level: 0,
        }
    }

    fn new_prime_input(id: usize) -> Self {
        Self {
            id,
            typ: AigNodeType::PrimeInput,
            fanouts: Vec::new(),
            level: 0,
        }
    }

    fn new_latch_input(id: usize) -> Self {
        Self {
            id,
            typ: AigNodeType::LatchInput,
            fanouts: Vec::new(),
            level: 0,
        }
    }

    fn new_and(id: usize, mut fanin0: AigEdge, mut fanin1: AigEdge, level: usize) -> Self {
        if fanin0.node_id() > fanin1.node_id() {
            swap(&mut fanin0, &mut fanin1);
        }
        Self {
            id,
            typ: AigNodeType::And(fanin0, fanin1),
            fanouts: Vec::new(),
            level,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Aig {
    pub nodes: Vec<AigNode>,
    pub inputs: Vec<AigNodeId>,
    pub latchs: Vec<AigLatch>,
    pub outputs: Vec<AigEdge>,
    pub bads: Vec<AigEdge>,
    pub constraints: Vec<AigEdge>,
}

impl Aig {
    pub fn new() -> Self {
        Self {
            nodes: vec![AigNode::new_false(0)],
            inputs: Vec::new(),
            latchs: Vec::new(),
            outputs: Vec::new(),
            bads: Vec::new(),
            constraints: Vec::new(),
        }
    }

    pub fn new_input_node(&mut self) -> AigNodeId {
        let nodeid = self.nodes.len();
        let input = AigNode::new_prime_input(nodeid);
        self.nodes.push(input);
        self.inputs.push(nodeid);
        nodeid
    }

    #[inline]
    pub fn new_and_node(&mut self, mut fanin0: AigEdge, mut fanin1: AigEdge) -> AigEdge {
        if fanin0.node_id() > fanin1.node_id() {
            swap(&mut fanin0, &mut fanin1);
        }
        if fanin0 == AigEdge::constant_edge(true) {
            return fanin1;
        }
        if fanin0 == AigEdge::constant_edge(false) {
            return AigEdge::constant_edge(false);
        }
        if fanin1 == AigEdge::constant_edge(true) {
            return fanin0;
        }
        if fanin1 == AigEdge::constant_edge(false) {
            return AigEdge::constant_edge(false);
        }
        if fanin0 == fanin1 {
            fanin0
        } else if fanin0 == !fanin1 {
            AigEdge::constant_edge(false)
        } else {
            let nodeid = self.nodes.len();
            let level = self.nodes[fanin0.node_id()]
                .level
                .max(self.nodes[fanin1.node_id()].level)
                + 1;
            let and = AigNode::new_and(nodeid, fanin0, fanin1, level);
            self.nodes.push(and);
            self.nodes[fanin0.id]
                .fanouts
                .push(AigEdge::new(nodeid, fanin0.compl()));
            self.nodes[fanin1.id]
                .fanouts
                .push(AigEdge::new(nodeid, fanin1.compl()));
            nodeid.into()
        }
    }

    pub fn new_or_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        !self.new_and_node(!fanin0, !fanin1)
    }

    pub fn new_equal_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        let node1 = self.new_and_node(fanin0, !fanin1);
        let node2 = self.new_and_node(!fanin0, fanin1);
        let edge1 = !node1;
        let edge2 = !node2;
        self.new_and_node(edge1, edge2)
    }

    pub fn new_and_nodes<I: IntoIterator<Item = AigEdge>>(&mut self, edges: I) -> AigEdge {
        let mut heap = BinaryHeap::new();
        for edge in edges {
            heap.push(Reverse((self.nodes[edge.node_id()].level, edge)));
        }
        while heap.len() > 1 {
            let peek0 = heap.pop().unwrap().0 .1;
            let peek1 = heap.pop().unwrap().0 .1;
            let new_node = self.new_and_node(peek0, peek1);
            heap.push(Reverse((self.nodes[new_node.node_id()].level, new_node)));
        }
        heap.pop().unwrap().0 .1
    }

    pub fn merge_fe_node(&mut self, replaced: AigEdge, by: AigEdge) {
        let compl = replaced.compl() != by.compl();
        let replaced = replaced.node_id();
        let by = by.node_id();
        assert!(replaced > by);
        self.nodes[by].fanouts.retain(|e| e.node_id() != replaced);
        let fanouts = take(&mut self.nodes[replaced].fanouts);
        for fanout in fanouts {
            let fanout_node_id = fanout.node_id();
            let mut fanin0 = self.nodes[fanout_node_id].fanin0();
            let mut fanin1 = self.nodes[fanout_node_id].fanin1();
            assert!(fanin0.node_id() < fanin1.node_id());
            // self.strash.remove(fanin0, fanin1);
            if fanin0.node_id() == replaced {
                assert_eq!(fanout.compl(), fanin0.compl());
                fanin0 = AigEdge::new(by, fanout.compl() ^ compl);
            }
            if fanin1.node_id() == replaced {
                assert_eq!(fanout.compl(), fanin1.compl());
                fanin1 = AigEdge::new(by, fanout.compl() ^ compl);
            }
            if fanin0.node_id() > fanin1.node_id() {
                swap(&mut fanin0, &mut fanin1);
            }
            self.nodes[fanout_node_id].set_fanin0(fanin0);
            self.nodes[fanout_node_id].set_fanin1(fanin1);

            self.nodes[fanout_node_id].level = self.nodes[fanin0.node_id()]
                .level
                .max(self.nodes[fanin1.node_id()].level)
                + 1;
            self.nodes[by].fanouts.push(fanout);
        }
        for latch in &mut self.latchs {
            if latch.next.node_id() == replaced {
                latch.next.set_nodeid(by);
                if compl {
                    latch.next = !latch.next;
                }
            }
        }
        for out in &mut self.outputs {
            if out.node_id() == replaced {
                out.set_nodeid(by);
                if compl {
                    *out = !*out
                }
            }
        }
        for bad in &mut self.bads {
            if bad.node_id() == replaced {
                bad.set_nodeid(by);
                if compl {
                    *bad = !*bad
                }
            }
        }
    }
}

impl Aig {
    pub fn num_nodes(&self) -> usize {
        self.nodes.len()
    }

    pub fn nodes_range(&self) -> Range<usize> {
        1..self.num_nodes()
    }

    pub fn nodes_range_with_false(&self) -> Range<usize> {
        0..self.num_nodes()
    }

    pub fn ands_iter(&self) -> impl Iterator<Item = &AigNode> {
        self.nodes
            .iter()
            .filter(|node| matches!(node.typ, AigNodeType::And(_, _)))
    }

    pub fn ands_iter_mut(&mut self) -> impl Iterator<Item = &mut AigNode> {
        self.nodes
            .iter_mut()
            .filter(|node| matches!(node.typ, AigNodeType::And(_, _)))
    }

    pub fn fanin_logic_cone<'a, I: IntoIterator<Item = &'a AigEdge>>(&self, logic: I) -> Vec<bool> {
        let mut flag = vec![false; self.num_nodes()];
        for l in logic {
            flag[l.node_id()] = true;
        }
        for id in self.nodes_range_with_false().rev() {
            if flag[id] && self.nodes[id].is_and() {
                flag[self.nodes[id].fanin0().node_id()] = true;
                flag[self.nodes[id].fanin1().node_id()] = true;
            }
        }
        flag
    }

    pub fn fanout_logic_cone(&self, logic: AigEdge) -> Vec<bool> {
        let mut flag = vec![false; self.num_nodes()];
        flag[logic.node_id()] = true;
        for id in self.nodes_range_with_false() {
            if flag[id] {
                for f in &self.nodes[id].fanouts {
                    flag[f.node_id()] = true;
                }
            }
        }
        flag
    }
}

impl Aig {
    pub fn transfer_latch_outputs_into_pinputs(
        &mut self,
    ) -> (Vec<(AigNodeId, AigNodeId)>, AigEdge) {
        let latchs = take(&mut self.latchs);
        let mut equals = Vec::new();
        (
            latchs
                .iter()
                .map(|l| {
                    assert!(self.nodes[l.input].is_latch_input());
                    self.nodes[l.input].typ = AigNodeType::PrimeInput;
                    let inode = self.new_input_node();
                    let equal_node = self.new_equal_node(l.next, inode.into());
                    equals.push(equal_node);
                    (inode, l.input)
                })
                .collect(),
            self.new_and_nodes(equals),
        )
    }
}

impl Default for Aig {
    fn default() -> Self {
        Self::new()
    }
}

impl Index<AigNodeId> for Aig {
    type Output = AigNode;

    fn index(&self, index: AigNodeId) -> &Self::Output {
        &self.nodes[index]
    }
}
