use crate::{Aig, AigEdge};
use logic_form::{Clause, Cnf, Lit};
use std::collections::HashSet;

impl Aig {
    pub fn get_cnf(&self, root: AigEdge) -> Cnf {
        assert!(root != AigEdge::constant_edge(true) && root != AigEdge::constant_edge(false));
        let mut refs = HashSet::new();
        refs.insert(root);
        let mut ans = Cnf::new();
        for i in self.nodes_range().rev() {
            let edge: AigEdge = self.nodes[i].node_id().into();
            if self.nodes[i].is_and() {
                if refs.contains(&edge) {
                    refs.insert(self.nodes[i].fanin0());
                    refs.insert(self.nodes[i].fanin1());
                    ans.push(Clause::from([
                        Lit::new(self.nodes[i].node_id().into(), true),
                        Lit::new(
                            self.nodes[i].fanin0().node_id().into(),
                            self.nodes[i].fanin0().compl(),
                        ),
                    ]));
                    ans.push(Clause::from([
                        Lit::new(self.nodes[i].node_id().into(), true),
                        Lit::new(
                            self.nodes[i].fanin1().node_id().into(),
                            self.nodes[i].fanin1().compl(),
                        ),
                    ]));
                }
                if refs.contains(&!edge) {
                    refs.insert(!self.nodes[i].fanin0());
                    refs.insert(!self.nodes[i].fanin1());
                    ans.push(Clause::from([
                        Lit::new(self.nodes[i].node_id().into(), false),
                        Lit::new(
                            self.nodes[i].fanin0().node_id().into(),
                            !self.nodes[i].fanin0().compl(),
                        ),
                        Lit::new(
                            self.nodes[i].fanin1().node_id().into(),
                            !self.nodes[i].fanin1().compl(),
                        ),
                    ]));
                }
            }
        }
        ans.push(Clause::from([Lit::new(
            root.node_id().into(),
            root.compl(),
        )]));
        ans
    }
}
