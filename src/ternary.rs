use crate::{Aig, AigEdge};
use logic_form::ternary::TernaryValue;

impl Aig {
    pub fn ternary_simulate(
        &self,
        input: &[TernaryValue],
        state: &[TernaryValue],
    ) -> Vec<TernaryValue> {
        assert!(input.len() == self.inputs.len());
        assert!(state.len() == self.latchs.len());
        let mut ans = vec![TernaryValue::default(); self.nodes.len()];
        ans[0] = TernaryValue::False;
        for i in 0..self.inputs.len() {
            ans[self.inputs[i]] = input[i];
        }
        for i in 0..self.latchs.len() {
            ans[self.latchs[i].input] = state[i];
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
}

pub struct TernarySimulate<'a> {
    aig: &'a Aig,
    state: Vec<TernaryValue>,
    value: Vec<TernaryValue>,
}

impl<'a> TernarySimulate<'a> {
    pub fn new(aig: &'a Aig, state: Vec<TernaryValue>) -> Self {
        assert!(state.len() == aig.latchs.len());
        Self {
            aig,
            state,
            value: Default::default(),
        }
    }

    pub fn simulate(&mut self, input: Vec<TernaryValue>) {
        self.value = self.aig.ternary_simulate(&input, &self.state);
        for i in 0..self.aig.latchs.len() {
            let ln = self.aig.latchs[i].next;
            self.state[i] = self.value[ln.id].not_if(ln.compl());
        }
    }

    pub fn value(&self, e: AigEdge) -> TernaryValue {
        self.value[e.node_id()].not_if(e.compl())
    }
}
