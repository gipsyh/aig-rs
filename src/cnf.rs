use crate::{Aig, AigEdge};
use giputils::hash::GHashSet;
use logic_form::{DagCnf, LitVvec, Var};

impl Aig {
    #[inline]
    fn get_root_refs(&self) -> GHashSet<usize> {
        let mut refs = GHashSet::new();
        for l in self.latchs.iter() {
            refs.insert(l.next.node_id());
        }
        for l in self
            .constraints
            .iter()
            .chain(self.bads.iter())
            .chain(self.outputs.iter())
            .chain(self.justice.iter().flatten())
            .chain(self.fairness.iter())
        {
            refs.insert(l.node_id());
        }
        refs
    }

    fn is_xor(&self, n: usize) -> Option<(AigEdge, AigEdge)> {
        if !self.nodes[n].is_and() {
            return None;
        }
        let (fanin0, fanin1) = self.nodes[n].fanin();
        if !fanin0.compl()
            || !fanin1.compl()
            || !self.nodes[fanin0.node_id()].is_and()
            || !self.nodes[fanin1.node_id()].is_and()
        {
            return None;
        }
        let (fanin00, fanin01) = self.nodes[fanin0.node_id()].fanin();
        let (fanin10, fanin11) = self.nodes[fanin1.node_id()].fanin();
        if fanin00 == !fanin10 && fanin01 == !fanin11 {
            if fanin00.node_id() == fanin01.node_id() {
                return None;
            }
            return Some((fanin00, fanin01));
        }
        None
    }

    fn is_ite(&self, n: usize) -> Option<(AigEdge, AigEdge, AigEdge)> {
        if !self.nodes[n].is_and() {
            return None;
        }
        let (fanin0, fanin1) = self.nodes[n].fanin();
        if !fanin0.compl()
            || !fanin1.compl()
            || !self.nodes[fanin0.node_id()].is_and()
            || !self.nodes[fanin1.node_id()].is_and()
        {
            return None;
        }
        let (fanin00, fanin01) = self.nodes[fanin0.node_id()].fanin();
        let (fanin10, fanin11) = self.nodes[fanin1.node_id()].fanin();

        let (i, t, e) = if fanin00 == !fanin10 {
            (fanin00, !fanin01, !fanin11)
        } else if fanin00 == !fanin11 {
            (fanin00, !fanin01, !fanin10)
        } else if fanin01 == !fanin10 {
            (fanin01, !fanin00, !fanin11)
        } else if fanin01 == !fanin11 {
            (fanin01, !fanin00, !fanin10)
        } else {
            return None;
        };
        if i.node_id() == t.node_id() || i.node_id() == e.node_id() || t.node_id() == e.node_id() {
            return None;
        }
        Some((i, t, e))
    }

    pub fn cnf(&self, optimize: bool) -> DagCnf {
        let mut refs = self.get_root_refs();
        let mut ans = DagCnf::new();
        for node in self.nodes.iter().skip(1) {
            assert_eq!(Var::new(node.node_id()), ans.new_var());
        }
        for i in self.nodes_range().rev() {
            if self.nodes[i].is_and() && (refs.contains(&i)) {
                let n = Var::new(self.nodes[i].node_id()).lit();
                if optimize {
                    if let Some((xor0, xor1)) = self.is_xor(i) {
                        refs.insert(xor0.node_id());
                        refs.insert(xor1.node_id());
                        let xor0 = xor0.to_lit();
                        let xor1 = xor1.to_lit();
                        ans.add_rel(n.var(), &LitVvec::cnf_xor(n, xor0, xor1));
                        continue;
                    }
                    if let Some((c, t, e)) = self.is_ite(i) {
                        refs.insert(c.node_id());
                        refs.insert(t.node_id());
                        refs.insert(e.node_id());
                        let c = c.to_lit();
                        let t = t.to_lit();
                        let e = e.to_lit();
                        ans.add_rel(n.var(), &LitVvec::cnf_ite(n, c, t, e));
                        continue;
                    }
                }
                refs.insert(self.nodes[i].fanin0().id);
                refs.insert(self.nodes[i].fanin1().id);
                let fanin0 = self.nodes[i].fanin0().to_lit();
                let fanin1 = self.nodes[i].fanin1().to_lit();
                ans.add_rel(n.var(), &LitVvec::cnf_and(n, &[fanin0, fanin1]));
            }
        }
        ans
    }
}
