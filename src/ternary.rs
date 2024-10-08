use crate::Aig;
use std::{
    fmt::{self, Display, Formatter},
    ops::{BitAnd, BitOr, Not},
};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TernaryValue {
    True,
    False,
    X,
}

impl Default for TernaryValue {
    fn default() -> Self {
        Self::X
    }
}

impl Not for TernaryValue {
    type Output = TernaryValue;

    fn not(self) -> Self::Output {
        match self {
            TernaryValue::True => TernaryValue::False,
            TernaryValue::False => TernaryValue::True,
            TernaryValue::X => TernaryValue::X,
        }
    }
}

impl BitAnd for TernaryValue {
    type Output = TernaryValue;

    fn bitand(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (TernaryValue::True, TernaryValue::True) => TernaryValue::True,
            (TernaryValue::True, TernaryValue::False) => TernaryValue::False,
            (TernaryValue::True, TernaryValue::X) => TernaryValue::X,
            (TernaryValue::False, TernaryValue::True) => TernaryValue::False,
            (TernaryValue::False, TernaryValue::False) => TernaryValue::False,
            (TernaryValue::False, TernaryValue::X) => TernaryValue::False,
            (TernaryValue::X, TernaryValue::True) => TernaryValue::X,
            (TernaryValue::X, TernaryValue::False) => TernaryValue::False,
            (TernaryValue::X, TernaryValue::X) => TernaryValue::X,
        }
    }
}

impl BitOr for TernaryValue {
    type Output = TernaryValue;

    fn bitor(self, rhs: Self) -> Self::Output {
        match (self, rhs) {
            (TernaryValue::True, TernaryValue::True) => TernaryValue::True,
            (TernaryValue::True, TernaryValue::False) => TernaryValue::True,
            (TernaryValue::True, TernaryValue::X) => TernaryValue::True,
            (TernaryValue::False, TernaryValue::True) => TernaryValue::True,
            (TernaryValue::False, TernaryValue::False) => TernaryValue::False,
            (TernaryValue::False, TernaryValue::X) => TernaryValue::X,
            (TernaryValue::X, TernaryValue::True) => TernaryValue::True,
            (TernaryValue::X, TernaryValue::False) => TernaryValue::X,
            (TernaryValue::X, TernaryValue::X) => TernaryValue::X,
        }
    }
}

impl TernaryValue {
    pub fn not_if(self, x: bool) -> Self {
        if x {
            !self
        } else {
            self
        }
    }
}

impl From<bool> for TernaryValue {
    fn from(value: bool) -> Self {
        if value {
            TernaryValue::True
        } else {
            TernaryValue::False
        }
    }
}

impl From<char> for TernaryValue {
    #[inline]
    fn from(value: char) -> Self {
        match value {
            '1' => Self::True,
            '0' => Self::False,
            'x' => Self::X,
            'X' => Self::X,
            _ => panic!(),
        }
    }
}

impl Display for TernaryValue {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        match self {
            TernaryValue::True => '1'.fmt(f),
            TernaryValue::False => '0'.fmt(f),
            TernaryValue::X => 'X'.fmt(f),
        }
    }
}

impl Aig {
    pub fn ternary_simulate(
        &self,
        primary_inputs: &[TernaryValue],
        latch_inputs: &[TernaryValue],
    ) -> Vec<TernaryValue> {
        assert!(primary_inputs.len() == self.inputs.len());
        assert!(latch_inputs.len() == self.latchs.len());
        let mut ans = vec![TernaryValue::default(); self.nodes.len()];
        ans[0] = TernaryValue::False;
        for i in 0..self.inputs.len() {
            ans[self.inputs[i]] = primary_inputs[i];
        }
        for i in 0..self.latchs.len() {
            ans[self.latchs[i].input] = latch_inputs[i];
        }
        for i in self.nodes_range() {
            if self.nodes[i].is_and() {
                let fanin0 =
                    ans[self.nodes[i].fanin0().node_id()].not_if(self.nodes[i].fanin0().compl());
                let fanin1 =
                    ans[self.nodes[i].fanin1().node_id()].not_if(self.nodes[i].fanin1().compl());
                ans[i] = fanin0 & fanin1;
            }
        }
        ans
    }

    // pub fn update_ternary_simulate(
    //     &self,
    //     mut simulation: Vec<TernaryValue>,
    //     input: AigNodeId,
    //     value: TernaryValue,
    // ) -> Vec<TernaryValue> {
    //     assert!(simulation[input] != value);
    //     simulation[input] = value;
    //     let mut queue = VecDeque::new();
    //     for out in self.nodes[input].fanouts.iter() {
    //         queue.push_back(out.node_id());
    //     }
    //     while let Some(node) = queue.pop_front() {
    //         let fanin0 = simulation[self.nodes[node].fanin0().node_id()]
    //             .not_if(self.nodes[node].fanin0().compl());
    //         let fanin1 = simulation[self.nodes[node].fanin1().node_id()]
    //             .not_if(self.nodes[node].fanin1().compl());
    //         let value = fanin0 & fanin1;
    //         if value != simulation[node] {
    //             simulation[node] = value;
    //             for out in self.nodes[node].fanouts.iter() {
    //                 queue.push_back(out.node_id());
    //             }
    //         }
    //     }
    //     simulation
    // }
}

impl Aig {
    pub fn test(&self) {
        let primary_inputs = vec![TernaryValue::X; self.inputs.len()];
        let mut latch_inputs = Vec::new();
        for l in self.latchs.iter() {
            latch_inputs.push(match l.init {
                Some(w) => TernaryValue::from(w),
                None => TernaryValue::X,
            });
        }
        let sim = self.ternary_simulate(&primary_inputs, &latch_inputs);
        let mut ans = Vec::new();
        for l in self.latchs.iter() {
            ans.push(sim[l.next.node_id()]);
        }
        dbg!(ans);
        todo!();
    }
}
