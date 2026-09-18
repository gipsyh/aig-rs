use crate::{Aig, AigEdge};
use giputils::gvec::Gvec;
use logicrs::{DagCnf, Lit, LitVvec, Var};

impl Aig {
    #[inline]
    fn get_root_refs(&self) -> Gvec<bool> {
        let mut refs = Gvec::from(vec![false; self.num_nodes()]);
        for l in self.latchs.iter() {
            refs[*l.next.var()] = true;
            if let Some(init) = &l.init {
                refs[*init.var()] = true;
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
            refs[*l.var()] = true;
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
        ans.new_var_to(Var::new(self.num_nodes() - 1));
        for i in self.nodes_range().rev() {
            if self.nodes[i].is_and() && refs[i] {
                let n = Var::new(i).lit();
                if optimize {
                    if let Some((xor0, xor1)) = self.is_xor(i) {
                        refs[*xor0.var()] = true;
                        refs[*xor1.var()] = true;
                        let xor0 = xor0.into();
                        let xor1 = xor1.into();
                        ans.add_rel_owned(n.var(), LitVvec::cnf_xor(n, xor0, xor1));
                        continue;
                    }
                    if let Some((c, t, e)) = self.is_ite(i) {
                        refs[*c.var()] = true;
                        refs[*t.var()] = true;
                        refs[*e.var()] = true;
                        let c = c.into();
                        let t = t.into();
                        let e = e.into();
                        ans.add_rel_owned(n.var(), LitVvec::cnf_ite(n, c, t, e));
                        continue;
                    }
                }
                let fanin0 = self.nodes[i].fanin0();
                let fanin1 = self.nodes[i].fanin1();
                refs[*fanin0.var()] = true;
                refs[*fanin1.var()] = true;
                ans.add_rel_owned(
                    n.var(),
                    LitVvec::cnf_and(n, &[fanin0.into(), fanin1.into()]),
                );
            }
        }
        ans
    }

    /// Encode only the AIG nodes that survive gate recognition. The returned
    /// map translates original AIG variables to the dense CNF numbering; zero
    /// denotes an internal gate that was absorbed or is unreachable.
    pub fn cnf_compact(&self) -> (DagCnf, Gvec<Var>) {
        let mut refs = self.get_root_refs();
        for i in self.nodes_range().rev() {
            if !self.nodes[i].is_and() || !refs[i] {
                continue;
            }
            if let Some((x, y)) = self.is_xor(i) {
                refs[*x.var()] = true;
                refs[*y.var()] = true;
                continue;
            }
            if let Some((c, t, e)) = self.is_ite(i) {
                refs[*c.var()] = true;
                refs[*t.var()] = true;
                refs[*e.var()] = true;
                continue;
            }
            refs[*self.nodes[i].fanin0().var()] = true;
            refs[*self.nodes[i].fanin1().var()] = true;
        }

        let mut map = Gvec::from(vec![Var::CONST; self.num_nodes()]);
        let mut count = 0;
        for i in self.nodes_range() {
            if self.nodes[i].is_leaf() || (self.nodes[i].is_and() && refs[i]) {
                count += 1;
                map[i] = Var::new(count);
            }
        }
        let mut ans = DagCnf::new();
        ans.new_var_to(Var::new(count));
        let map_edge = |edge: AigEdge| -> Lit {
            Lit::from(edge).map_var(|v| {
                let mapped = map[*v];
                assert!(v.is_constant() || !mapped.is_constant());
                mapped
            })
        };
        for i in self.nodes_range() {
            if !self.nodes[i].is_and() || !refs[i] {
                continue;
            }
            let n = map[i].lit();
            if let Some((x, y)) = self.is_xor(i) {
                ans.add_rel_owned(n.var(), LitVvec::cnf_xor(n, map_edge(x), map_edge(y)));
                continue;
            }
            if let Some((c, t, e)) = self.is_ite(i) {
                ans.add_rel_owned(
                    n.var(),
                    LitVvec::cnf_ite(n, map_edge(c), map_edge(t), map_edge(e)),
                );
                continue;
            }
            ans.add_rel_owned(
                n.var(),
                LitVvec::cnf_and(
                    n,
                    &[
                        map_edge(self.nodes[i].fanin0()),
                        map_edge(self.nodes[i].fanin1()),
                    ],
                ),
            );
        }
        (ans, map)
    }
}
