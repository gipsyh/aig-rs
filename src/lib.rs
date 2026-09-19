mod aiger;
pub mod cnf;
mod others;
mod strash;
mod ternary;

use giputils::{gvec::Gvec, hash::GHashMap};
use logicrs::{Lit, Var};
use std::{
    fmt,
    mem::swap,
    ops::{Index, Not, Range},
    vec,
};
pub use ternary::*;

#[derive(Clone, Copy, Hash, PartialEq, Eq)]
pub struct AigEdge(Lit);

impl fmt::Debug for AigEdge {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.0.fmt(f)
    }
}

impl Not for AigEdge {
    type Output = AigEdge;

    #[inline]
    fn not(self) -> Self::Output {
        Self(!self.0)
    }
}

impl From<usize> for AigEdge {
    #[inline]
    fn from(value: usize) -> Self {
        Self(Var::new(value).lit())
    }
}

impl From<Var> for AigEdge {
    #[inline]
    fn from(value: Var) -> Self {
        Self(value.lit())
    }
}

impl From<Lit> for AigEdge {
    #[inline]
    fn from(value: Lit) -> Self {
        Self(value)
    }
}

impl From<AigEdge> for Lit {
    #[inline]
    fn from(value: AigEdge) -> Self {
        value.0
    }
}

impl PartialOrd for AigEdge {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for AigEdge {
    #[inline]
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.var().cmp(&other.var())
    }
}

impl AigEdge {
    pub const NONE: AigEdge = AigEdge(Lit::NONE);

    #[inline]
    pub const fn is_none(&self) -> bool {
        self.0.is_none()
    }

    #[inline]
    pub const fn new(id: usize, complement: bool) -> Self {
        Self(Lit::new(Var::new(id), !complement))
    }

    #[inline]
    pub fn var(&self) -> Var {
        self.0.var()
    }

    #[inline]
    pub fn compl(&self) -> bool {
        !self.0.polarity()
    }

    #[inline]
    pub fn set_var(&mut self, v: Var) {
        self.0 = Lit::new(v, self.0.polarity());
    }

    #[inline]
    pub fn set_compl(&mut self, compl: bool) {
        self.0 = Lit::new(self.0.var(), !compl)
    }

    #[inline]
    pub fn not_if(self, x: bool) -> Self {
        Self(self.0.not_if(x))
    }

    #[inline]
    pub const fn constant(polarity: bool) -> Self {
        Self(Lit::constant(polarity))
    }

    #[inline]
    pub fn is_const(&self) -> bool {
        self.0.var().is_constant()
    }

    #[inline]
    pub fn is_constant(&self, polarity: bool) -> bool {
        self.0.is_constant(polarity)
    }

    #[inline]
    pub fn try_to_constant(self) -> Option<bool> {
        self.0.try_constant()
    }

    #[inline]
    pub fn to_constant(self) -> bool {
        self.try_to_constant().unwrap()
    }

    #[inline]
    pub fn map<M>(&self, map: &M) -> Self
    where
        M: Fn(Var) -> Var,
    {
        Self(self.0.map_var(map))
    }
}

#[derive(Debug, Clone, Copy)]
pub struct AigLatch {
    pub input: Var,
    pub next: AigEdge,
    pub init: Option<AigEdge>,
}

impl AigLatch {
    pub fn new(input: Var, next: AigEdge, init: Option<AigEdge>) -> Self {
        Self { input, next, init }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct AigNode {
    pub fanin0: AigEdge,
    pub fanin1: AigEdge,
}

impl AigNode {
    pub const LEAF: Self = Self {
        fanin0: AigEdge::NONE,
        fanin1: AigEdge::NONE,
    };

    #[inline]
    pub fn new_and(mut fanin0: AigEdge, mut fanin1: AigEdge) -> Self {
        debug_assert!(!fanin0.is_none() && !fanin1.is_none());
        if fanin0.var() > fanin1.var() {
            swap(&mut fanin0, &mut fanin1);
        }
        Self { fanin0, fanin1 }
    }

    #[inline]
    pub fn is_and(&self) -> bool {
        !self.is_leaf()
    }

    #[inline]
    pub fn is_leaf(&self) -> bool {
        *self == Self::LEAF
    }

    #[inline]
    pub fn fanin0(&self) -> AigEdge {
        if self.is_and() {
            self.fanin0
        } else {
            panic!("fanin0 called on non-AND node");
        }
    }

    #[inline]
    pub fn fanin1(&self) -> AigEdge {
        if self.is_and() {
            self.fanin1
        } else {
            panic!("fanin1 called on non-AND node");
        }
    }

    #[inline]
    pub fn fanin(&self) -> (AigEdge, AigEdge) {
        if self.is_and() {
            (self.fanin0, self.fanin1)
        } else {
            panic!("fanin called on non-AND node");
        }
    }

    #[inline]
    pub fn set_fanin0(&mut self, fanin: AigEdge) {
        if self.is_and() {
            self.fanin0 = fanin;
        } else {
            panic!("set_fanin0 called on non-AND node");
        }
    }

    #[inline]
    pub fn set_fanin1(&mut self, fanin: AigEdge) {
        if self.is_and() {
            self.fanin1 = fanin;
        } else {
            panic!("set_fanin1 called on non-AND node");
        }
    }

    #[inline]
    pub fn map<M>(&self, map: &M) -> Self
    where
        M: Fn(Var) -> Var,
    {
        if self.is_and() {
            Self {
                fanin0: self.fanin0.map(map),
                fanin1: self.fanin1.map(map),
            }
        } else {
            panic!();
        }
    }
}

#[derive(Debug, Clone)]
pub struct Aig {
    pub nodes: Gvec<AigNode>,
    pub inputs: Vec<Var>,
    pub latchs: Vec<AigLatch>,
    pub outputs: Vec<AigEdge>,
    pub bads: Vec<AigEdge>,
    pub constraints: Vec<AigEdge>,
    pub justice: Vec<Vec<AigEdge>>,
    pub fairness: Vec<AigEdge>,
    pub symbols: GHashMap<Var, String>,
}

impl Aig {
    pub fn new() -> Self {
        Self {
            nodes: vec![AigNode::LEAF].into(),
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

    pub fn new_leaf_node(&mut self) -> Var {
        let id = Var::new(self.nodes.len());
        self.nodes.push(AigNode::LEAF);
        id
    }

    #[inline]
    pub fn new_input(&mut self) -> Var {
        let input = self.new_leaf_node();
        self.inputs.push(input);
        input
    }

    #[inline]
    pub fn add_input(&mut self, input: Var) {
        self.inputs.push(input);
    }

    #[inline]
    pub fn new_latch(&mut self, next: AigEdge, init: Option<AigEdge>) -> Var {
        let input = self.new_leaf_node();
        self.latchs.push(AigLatch::new(input, next, init));
        input
    }

    #[inline]
    pub fn add_latch(&mut self, input: Var, next: AigEdge, init: Option<AigEdge>) {
        self.latchs.push(AigLatch::new(input, next, init))
    }

    #[inline]
    pub fn trivial_new_and_node(&mut self, fanin0: AigEdge, fanin1: AigEdge) -> AigEdge {
        let nodeid = self.nodes.len();
        let and = AigNode::new_and(fanin0, fanin1);
        self.nodes.push(and);
        nodeid.into()
    }

    #[inline]
    pub fn new_and_node(&mut self, mut fanin0: AigEdge, mut fanin1: AigEdge) -> AigEdge {
        if fanin0.var() > fanin1.var() {
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
    pub fn get_symbol(&self, v: Var) -> Option<String> {
        self.symbols.get(&v).cloned()
    }

    #[inline]
    pub fn set_symbol(&mut self, v: Var, s: &str) {
        self.symbols.insert(v, s.to_string());
    }
}

impl Aig {
    pub fn num_nodes(&self) -> u32 {
        self.nodes.len() as _
    }

    pub fn nodes_range(&self) -> Range<u32> {
        1..self.num_nodes()
    }

    pub fn nodes_range_with_false(&self) -> Range<u32> {
        0..self.num_nodes()
    }

    pub fn fanin_logic_cone<'a, I: IntoIterator<Item = &'a AigEdge>>(
        &self,
        logic: I,
    ) -> Gvec<bool> {
        let mut flag = Gvec::from(vec![false; self.num_nodes() as _]);
        for l in logic {
            flag[*l.var()] = true;
        }
        for id in self.nodes_range_with_false().rev() {
            if flag[id] && self.nodes[id].is_and() {
                flag[*self.nodes[id].fanin0().var()] = true;
                flag[*self.nodes[id].fanin1().var()] = true;
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
