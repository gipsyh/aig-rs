use crate::{Aig, AigEdge};
use giputils::hash::GHashSet;
use logicrs::{DagCnf, LitVvec, Var};

impl Aig {
    #[inline]
    fn get_root_refs(&self) -> GHashSet<Var> {
        let mut refs = GHashSet::new();
        for l in self.latchs.iter() {
            refs.insert(l.next.var());
            if let Some(init) = &l.init {
                refs.insert(init.var());
            }
        }
        for l in self
            .constraints
            .iter()
            .chain(self.bads.iter())
            .chain(self.outputs.iter())
            .chain(self.justice.iter().flatten())
            .chain(self.fairness.iter())
        {
            refs.insert(l.var());
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
            || !self.nodes[*fanin0.var()].is_and()
            || !self.nodes[*fanin1.var()].is_and()
        {
            return None;
        }
        let (fanin00, fanin01) = self.nodes[*fanin0.var()].fanin();
        let (fanin10, fanin11) = self.nodes[*fanin1.var()].fanin();
        if fanin00 == !fanin10 && fanin01 == !fanin11 {
            if fanin00.var() == fanin01.var() {
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
            || !self.nodes[*fanin0.var()].is_and()
            || !self.nodes[*fanin1.var()].is_and()
        {
            return None;
        }
        let (fanin00, fanin01) = self.nodes[*fanin0.var()].fanin();
        let (fanin10, fanin11) = self.nodes[*fanin1.var()].fanin();

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
        if i.var() == t.var() || i.var() == e.var() || t.var() == e.var() {
            return None;
        }
        Some((i, t, e))
    }

    pub fn cnf(&self, optimize: bool) -> DagCnf {
        let mut refs = self.get_root_refs();
        let mut ans = DagCnf::new();
        for (id, _) in self.nodes.iter().enumerate().skip(1) {
            assert_eq!(Var::new(id), ans.new_var());
        }
        for i in self.nodes_range().rev() {
            if self.nodes[i].is_and() && (refs.contains(&Var::new(i))) {
                let n = Var::new(i).lit();
                if optimize {
                    if let Some((xor0, xor1)) = self.is_xor(i) {
                        refs.insert(xor0.var());
                        refs.insert(xor1.var());
                        let xor0 = xor0.to_lit();
                        let xor1 = xor1.to_lit();
                        ans.add_rel(n.var(), &LitVvec::cnf_xor(n, xor0, xor1));
                        continue;
                    }
                    if let Some((c, t, e)) = self.is_ite(i) {
                        refs.insert(c.var());
                        refs.insert(t.var());
                        refs.insert(e.var());
                        let c = c.to_lit();
                        let t = t.to_lit();
                        let e = e.to_lit();
                        ans.add_rel(n.var(), &LitVvec::cnf_ite(n, c, t, e));
                        continue;
                    }
                }
                let fanin0 = self.nodes[i].fanin0();
                let fanin1 = self.nodes[i].fanin1();
                refs.insert(fanin0.var());
                refs.insert(fanin1.var());
                ans.add_rel(
                    n.var(),
                    &LitVvec::cnf_and(n, &[fanin0.to_lit(), fanin1.to_lit()]),
                );
            }
        }
        ans
    }
}
