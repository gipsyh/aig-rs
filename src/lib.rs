mod aiger;
mod cnf;
mod display;
mod logic_form;
mod others;
mod simplify;
mod ternary;

pub use crate::logic_form::*;
use ::logic_form::Lit;
use std::{
    mem::swap,
    ops::{Index, Not, Range},
    vec,
};
pub use ternary::*;

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

#[derive(Debug, Clone, Copy)]
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
    Input,
    And(AigEdge, AigEdge),
}

#[derive(Debug, Clone)]
pub struct AigNode {
    id: AigNodeId,
    typ: AigNodeType,
    pub fanouts: Vec<AigEdge>,
}

impl AigNode {
    pub fn node_id(&self) -> AigNodeId {
        self.id
    }

    pub fn is_and(&self) -> bool {
        matches!(self.typ, AigNodeType::And(_, _))
    }

    pub fn is_input(&self) -> bool {
        matches!(self.typ, AigNodeType::Input)
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
        }
    }

    fn new_input(id: usize) -> Self {
        Self {
            id,
            typ: AigNodeType::Input,
            fanouts: Vec::new(),
        }
    }

    fn new_and(id: usize, mut fanin0: AigEdge, mut fanin1: AigEdge) -> Self {
        if fanin0.node_id() > fanin1.node_id() {
            swap(&mut fanin0, &mut fanin1);
        }
        Self {
            id,
            typ: AigNodeType::And(fanin0, fanin1),
            fanouts: Vec::new(),
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
        let input = AigNode::new_input(nodeid);
        self.nodes.push(input);
        nodeid
    }
    pub fn new_latch(&mut self, input: AigNodeId, next: AigEdge, init: Option<bool>) {
        self.latchs.push(AigLatch::new(input, next, init))
    }

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
            let and = AigNode::new_and(nodeid, fanin0, fanin1);
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
