use crate::{Aig, AigEdge};
use logic_form::{Clause, Cnf, Lit};
use std::collections::HashSet;

impl Aig {
    pub fn get_cnf(&self, logic: &[AigEdge]) -> Cnf {
        let mut refs = HashSet::new();
        for l in logic {
            refs.insert(l.node_id());
        }
        let mut ans = Cnf::new();
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
}
