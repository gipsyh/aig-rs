use crate::{Aig, AigEdge};
use logic_form::{Clause, Lit};
use std::collections::{HashMap, HashSet};

impl Aig {
    pub fn get_cnf(&self, logic: &[AigEdge]) -> Vec<Clause> {
        let mut refs = HashSet::new();
        for l in logic {
            refs.insert(l.node_id());
        }
        let mut ans = Vec::new();
        ans.push(Clause::from([Lit::constant_lit(true)]));
        for i in self.nodes_range().rev() {
            let edge: AigEdge = self.nodes[i].node_id().into();
            if self.nodes[i].is_and() && (refs.contains(&edge.id)) {
                refs.insert(self.nodes[i].fanin0().id);
                refs.insert(self.nodes[i].fanin1().id);
                ans.push(Clause::from([
                    Lit::new(self.nodes[i].node_id().into(), false),
                    Lit::new(
                        self.nodes[i].fanin0().node_id().into(),
                        !self.nodes[i].fanin0().compl(),
                    ),
                ]));
                ans.push(Clause::from([
                    Lit::new(self.nodes[i].node_id().into(), false),
                    Lit::new(
                        self.nodes[i].fanin1().node_id().into(),
                        !self.nodes[i].fanin1().compl(),
                    ),
                ]));
                ans.push(Clause::from([
                    Lit::new(self.nodes[i].node_id().into(), true),
                    Lit::new(
                        self.nodes[i].fanin0().node_id().into(),
                        self.nodes[i].fanin0().compl(),
                    ),
                    Lit::new(
                        self.nodes[i].fanin1().node_id().into(),
                        self.nodes[i].fanin1().compl(),
                    ),
                ]));
            }
        }
        ans
    }

    pub fn get_optimized_cnf(&self, logic: &[AigEdge]) -> Vec<Clause> {
        let mut latchs = HashMap::new();
        for l in self.latchs.iter() {
            latchs.insert(l.input, *l);
        }
        let mut refs = HashSet::new();
        let mut queue = Vec::new();
        for l in logic {
            if !refs.contains(l) {
                refs.insert(*l);
                queue.push(*l);
            }
        }
        let mut ans = Vec::new();
        while let Some(e) = queue.pop() {
            let i = e.node_id();
            let mut add_ref = |e: AigEdge| {
                if !refs.contains(&e) {
                    refs.insert(e);
                    queue.push(e);
                }
            };
            if self.nodes[i].is_and() {
                if !e.compl() {
                    add_ref(self.nodes[i].fanin0());
                    add_ref(self.nodes[i].fanin1());
                    ans.push(Clause::from([
                        Lit::new(self.nodes[i].node_id().into(), false),
                        Lit::new(
                            self.nodes[i].fanin0().node_id().into(),
                            !self.nodes[i].fanin0().compl(),
                        ),
                    ]));
                    ans.push(Clause::from([
                        Lit::new(self.nodes[i].node_id().into(), false),
                        Lit::new(
                            self.nodes[i].fanin1().node_id().into(),
                            !self.nodes[i].fanin1().compl(),
                        ),
                    ]));
                } else {
                    add_ref(!self.nodes[i].fanin0());
                    add_ref(!self.nodes[i].fanin1());
                    ans.push(Clause::from([
                        Lit::new(self.nodes[i].node_id().into(), true),
                        Lit::new(
                            self.nodes[i].fanin0().node_id().into(),
                            self.nodes[i].fanin0().compl(),
                        ),
                        Lit::new(
                            self.nodes[i].fanin1().node_id().into(),
                            self.nodes[i].fanin1().compl(),
                        ),
                    ]));
                }
            } else if let Some(l) = latchs.get(&e.node_id()) {
                let mut next = l.next;
                if e.compl() {
                    next = !next;
                }
                add_ref(next);
            }
        }
        ans
    }
}
