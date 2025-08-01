mod aiger;
pub mod cnf;
mod others;
mod strash;
mod ternary;

use giputils::hash::GHashMap;
use logicrs::Lit;
use std::{
    mem::swap,
    ops::{Index, Not, Range},
    vec,
};
pub use ternary::*;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct AigEdge {
    id: usize,
    complement: bool,
}

impl Not for AigEdge {
    type Output = AigEdge;

    fn not(mut self) -> Self::Output {
        self.complement = !self.complement;
        self
    }
}

impl From<usize> for AigEdge {
    fn from(value: usize) -> Self {
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
    #[inline]
    pub fn new(id: usize, complement: bool) -> Self {
        Self { id, complement }
    }

    #[inline]
    pub fn node_id(&self) -> usize {
        self.id
    }

    #[inline]
    pub fn compl(&self) -> bool {
        self.complement
    }

    #[inline]
    pub fn set_nodeid(&mut self, nodeid: usize) {
        self.id = nodeid;
    }

    #[inline]
    pub fn set_compl(&mut self, compl: bool) {
        self.complement = compl
    }

    #[inline]
    pub fn not_if(self, x: bool) -> Self {
        if x { !self } else { self }
    }

    #[inline]
    pub fn constant(polarity: bool) -> Self {
        AigEdge {
            id: 0,
            complement: polarity,
        }
    }

    #[inline]
    pub fn is_const(&self) -> bool {
        self.id == 0
    }

    #[inline]
    pub fn is_constant(&self, polarity: bool) -> bool {
        *self == Self::constant(polarity)
    }

    #[inline]
    pub fn try_to_constant(self) -> Option<bool> {
        if self.is_constant(true) {
            Some(true)
        } else if self.is_constant(false) {
            Some(false)
        } else {
            None
        }
    }

    #[inline]
    pub fn to_constant(self) -> bool {
        self.try_to_constant().unwrap()
    }

    #[inline]
    pub fn from_lit(lit: Lit) -> Self {
        Self {
            id: lit.var().into(),
            complement: !lit.polarity(),
        }
    }

    #[inline]
    pub fn to_lit(&self) -> Lit {
        Lit::new(self.id.into(), !self.complement)
    }

    #[inline]
    pub fn map<M>(&self, map: &M) -> Self
    where
        M: Fn(usize) -> usize,
    {
        Self {
            id: map(self.id),
            complement: self.complement,
        }
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AigLatch {
    pub input: usize,
    pub next: AigEdge,
    pub init: Option<AigEdge>,
}

impl AigLatch {
    pub fn new(input: usize, next: AigEdge, init: Option<AigEdge>) -> Self {
        Self { input, next, init }
    }
}

#[derive(Debug, Clone)]
pub enum AigNodeType {
    False,
    Leaf,
    And(AigEdge, AigEdge),
}

#[derive(Debug, Clone)]
pub struct AigNode {
    id: usize,
    typ: AigNodeType,
}

impl AigNode {
    pub fn node_id(&self) -> usize {
        self.id
    }

    pub fn is_and(&self) -> bool {
        matches!(self.typ, AigNodeType::And(_, _))
    }

    pub fn is_leaf(&self) -> bool {
        matches!(self.typ, AigNodeType::Leaf)
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

    pub fn fanin(&self) -> (AigEdge, AigEdge) {
        let AigNodeType::And(fanin0, fanin1) = self.typ else {
            panic!();
        };
        (fanin0, fanin1)
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

    #[inline]
    pub fn map<M>(&self, map: &M) -> Self
    where
        M: Fn(usize) -> usize,
    {
        let mut res = self.clone();
        res.id = map(res.id);
        if let AigNodeType::And(fanin0, fanin1) = &mut res.typ {
            *fanin0 = fanin0.map(map);
            *fanin1 = fanin1.map(map);
        }
        res
    }
}

impl AigNode {
    fn new_and(id: usize, mut fanin0: AigEdge, mut fanin1: AigEdge) -> Self {
        if fanin0.node_id() > fanin1.node_id() {
            swap(&mut fanin0, &mut fanin1);
        }
        Self {
            id,
            typ: AigNodeType::And(fanin0, fanin1),
        }
    }
}

#[derive(Debug, Clone)]
pub struct Aig {
    pub nodes: Vec<AigNode>,
    pub inputs: Vec<usize>,
    pub latchs: Vec<AigLatch>,
    pub outputs: Vec<AigEdge>,
    pub bads: Vec<AigEdge>,
    pub constraints: Vec<AigEdge>,
    pub justice: Vec<Vec<AigEdge>>,
    pub fairness: Vec<AigEdge>,
    pub symbols: GHashMap<usize, String>,
}

impl Aig {
    pub fn new() -> Self {
        Self {
            nodes: vec![AigNode {
                id: 0,
                typ: AigNodeType::False,
            }],
            inputs: Vec::new(),
            latchs: Vec::new(),
            outputs: Vec::new(),
            bads: Vec::new(),
            constraints: Vec::new(),
            justice: Vec::new(),
            fairness: Vec::new(),
            symbols: Default::default(),
        }
    }

    pub fn new_leaf_node(&mut self) -> usize {
        let id = self.nodes.len();
        let leaf = AigNode {
            id,
            typ: AigNodeType::Leaf,
        };
        self.nodes.push(leaf);
        id
    }

    #[inline]
    pub fn new_input(&mut self) -> usize {
        let input = self.new_leaf_node();
        self.inputs.push(input);
        input
    }

    #[inline]
    pub fn add_input(&mut self, input: usize) {
        self.inputs.push(input);
    }

    #[inline]
    pub fn new_latch(&mut self, next: AigEdge, init: Option<AigEdge>) -> usize {
        let input = self.new_leaf_node();
        self.latchs.push(AigLatch::new(input, next, init));
        input
    }

    #[inline]
    pub fn add_latch(&mut self, input: usize, next: AigEdge, init: Option<AigEdge>) {
        self.latchs.push(AigLatch::new(input, next, init))
    }

    #[inline]
    pub fn trivial_new_and_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        let nodeid = self.nodes.len();
        let and = AigNode::new_and(nodeid, fanin0, fanin1);
        self.nodes.push(and);
        nodeid.into()
    }

    #[inline]
    pub fn new_and_node(&mut self, mut fanin0: AigEdge, mut fanin1: AigEdge) -> AigEdge {
        if fanin0.node_id() > fanin1.node_id() {
            swap(&mut fanin0, &mut fanin1);
        }
        if fanin0 == AigEdge::constant(true) {
            return fanin1;
        }
        if fanin0 == AigEdge::constant(false) {
            return AigEdge::constant(false);
        }
        if fanin1 == AigEdge::constant(true) {
            return fanin0;
        }
        if fanin1 == AigEdge::constant(false) {
            return AigEdge::constant(false);
        }
        if fanin0 == fanin1 {
            fanin0
        } else if fanin0 == !fanin1 {
            AigEdge::constant(false)
        } else {
            self.trivial_new_and_node(fanin0, fanin1)
        }
    }

    pub fn trivial_new_or_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        !self.trivial_new_and_node(!fanin0, !fanin1)
    }

    pub fn new_or_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        !self.new_and_node(!fanin0, !fanin1)
    }

    pub fn trivial_new_ands_node(&mut self, fanin: impl IntoIterator<Item = AigEdge>) -> AigEdge {
        let fanin: Vec<_> = fanin.into_iter().collect();
        if fanin.is_empty() {
            AigEdge::constant(true)
        } else if fanin.len() == 1 {
            fanin[0]
        } else {
            let mut res = self.trivial_new_and_node(fanin[0], fanin[1]);
            for &f in &fanin[2..] {
                res = self.trivial_new_and_node(res, f);
            }
            res
        }
    }

    pub fn new_ands_node(&mut self, fanin: impl IntoIterator<Item = AigEdge>) -> AigEdge {
        let fanin: Vec<_> = fanin.into_iter().collect();
        if fanin.is_empty() {
            AigEdge::constant(true)
        } else if fanin.len() == 1 {
            fanin[0]
        } else {
            let mut res = AigEdge::constant(true);
            for f in fanin {
                res = self.new_and_node(res, f);
            }
            res
        }
    }

    pub fn trivial_new_ors_node(&mut self, fanin: impl IntoIterator<Item = AigEdge>) -> AigEdge {
        !self.trivial_new_ands_node(fanin.into_iter().map(|e| !e))
    }

    pub fn new_ors_node(&mut self, fanin: impl IntoIterator<Item = AigEdge>) -> AigEdge {
        !self.new_ands_node(fanin.into_iter().map(|e| !e))
    }

    pub fn new_imply_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        self.new_or_node(!fanin0, fanin1)
    }

    pub fn new_eq_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        let x = self.new_and_node(fanin0, fanin1);
        let y = self.new_and_node(!fanin0, !fanin1);
        self.new_or_node(x, y)
    }

    #[inline]
    pub fn get_symbol(&self, id: usize) -> Option<String> {
        self.symbols.get(&id).cloned()
    }

    #[inline]
    pub fn set_symbol(&mut self, id: usize, s: &str) {
        self.symbols.insert(id, s.to_string());
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
}

impl Default for Aig {
    fn default() -> Self {
        Self::new()
    }
}

impl Index<usize> for Aig {
    type Output = AigNode;

    fn index(&self, index: usize) -> &Self::Output {
        &self.nodes[index]
    }
}
