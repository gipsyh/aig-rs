use crate::{Aig, AigEdge};
use giputils::gvec::Gvec;
use logicrs::{DagCnf, Lit, LitVec, LitVvec, Var};

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
        // Count uses in the recognized gate DAG, including external roots.
        // Values above one are equivalent for the inlining decision.
        let mut uses: Vec<u8> = refs.iter().map(|&root| u8::from(root)).collect();
        for i in self.nodes_range().rev() {
            if !self.nodes[i].is_and() || !refs[i] {
                continue;
            }
            let mut mark = |v: Var| {
                refs[*v] = true;
                let index = usize::from(v);
                uses[index] = uses[index].saturating_add(1);
            };
            if let Some((x, y)) = self.is_xor(i) {
                mark(x.var());
                mark(y.var());
                continue;
            }
            if let Some((c, t, e)) = self.is_ite(i) {
                mark(c.var());
                mark(t.var());
                mark(e.var());
                continue;
            }
            mark(self.nodes[i].fanin0().var());
            mark(self.nodes[i].fanin1().var());
        }

        // Inline a private ITE branch into its parent. Stop after one level
        // so that clauses contain at most four literals.
        let mut absorbed = Gvec::from(vec![false; self.num_nodes()]);
        for i in self.nodes_range().rev() {
            if !self.nodes[i].is_and() || !refs[i] || absorbed[i] {
                continue;
            }
            if let Some((_, t, e)) = self.is_ite(i) {
                for branch in [t, e] {
                    let child = usize::from(branch.var());
                    if uses[child] == 1 && self.is_ite(child).is_some() {
                        absorbed[child] = true;
                    }
                }
            }
        }

        let mut map = Gvec::from(vec![Var::CONST; self.num_nodes()]);
        let mut count = 0;
        for i in self.nodes_range() {
            if self.nodes[i].is_leaf() || (self.nodes[i].is_and() && refs[i] && !absorbed[i]) {
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
            if !self.nodes[i].is_and() || !refs[i] || absorbed[i] {
                continue;
            }
            let n = map[i].lit();
            if let Some((x, y)) = self.is_xor(i) {
                ans.add_rel_owned(n.var(), LitVvec::cnf_xor(n, map_edge(x), map_edge(y)));
                continue;
            }
            if let Some((c, t, e)) = self.is_ite(i) {
                let c = map_edge(c);
                if !absorbed[*t.var()] && !absorbed[*e.var()] {
                    ans.add_rel_owned(n.var(), LitVvec::cnf_ite(n, c, map_edge(t), map_edge(e)));
                } else {
                    let mut rel = LitVvec::new();
                    for (guard, branch) in [(!c, t), (c, e)] {
                        if absorbed[*branch.var()] {
                            let (select, then, otherwise) =
                                self.is_ite(usize::from(branch.var())).unwrap();
                            let select = map_edge(select);
                            for (child_guard, leaf) in [(!select, then), (select, otherwise)] {
                                let leaf = map_edge(leaf.not_if(branch.compl()));
                                rel.push(LitVec::from([guard, child_guard, !n, leaf]));
                                rel.push(LitVec::from([guard, child_guard, n, !leaf]));
                            }
                        } else {
                            let leaf = map_edge(branch);
                            rel.push(LitVec::from([guard, !n, leaf]));
                            rel.push(LitVec::from([guard, n, !leaf]));
                        }
                    }
                    ans.add_rel_owned(n.var(), rel);
                }
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

#[cfg(test)]
mod tests {
    use super::*;

    fn mux(aig: &mut Aig, select: AigEdge, then: AigEdge, otherwise: AigEdge) -> AigEdge {
        let on_then = aig.new_and_node(select, then);
        let on_else = aig.new_and_node(!select, otherwise);
        aig.new_or_node(on_then, on_else)
    }

    fn value(edge: AigEdge, values: &[bool]) -> bool {
        let base = if edge.var().is_constant() {
            false
        } else {
            values[usize::from(edge.var())]
        };
        base ^ edge.compl()
    }

    fn lit_value(lit: Lit, assignment: usize) -> bool {
        let base = if lit.var().is_constant() {
            false
        } else {
            (assignment >> (usize::from(lit.var()) - 1)) & 1 != 0
        };
        base == lit.polarity()
    }

    fn check_truth_table(aig: &Aig, cnf: &DagCnf, map: &Gvec<Var>) {
        assert!(cnf.num_var() <= 12);
        let mut satisfying = 0;
        let mut seen_inputs = vec![false; 1usize << aig.inputs.len()];
        for assignment in 0..(1usize << (cnf.num_var() - 1)) {
            if !cnf
                .clause()
                .all(|clause| clause.iter().any(|&lit| lit_value(lit, assignment)))
            {
                continue;
            }
            satisfying += 1;
            let mut values = vec![false; aig.num_nodes()];
            let mut input_assignment = 0usize;
            for (i, &input) in aig.inputs.iter().enumerate() {
                let bit = lit_value(map[*input].lit(), assignment);
                values[usize::from(input)] = bit;
                input_assignment |= usize::from(bit) << i;
            }
            assert!(!seen_inputs[input_assignment]);
            seen_inputs[input_assignment] = true;
            for i in aig.nodes_range() {
                if aig.nodes[i].is_and() {
                    let (left, right) = aig.nodes[i].fanin();
                    values[i] = value(left, &values) && value(right, &values);
                }
            }
            for &root in &aig.bads {
                let mapped = Lit::from(root).map_var(|v| map[*v]);
                assert_eq!(lit_value(mapped, assignment), value(root, &values));
            }
        }
        assert_eq!(satisfying, 1usize << aig.inputs.len());
        assert!(seen_inputs.iter().all(|&seen| seen));
    }

    #[test]
    fn inline_private_ite_branches() {
        for negate_branch in [false, true] {
            let mut aig = Aig::new();
            let inputs: Vec<_> = (0..5).map(|_| AigEdge::from(aig.new_input())).collect();
            let child = mux(&mut aig, inputs[1], inputs[2], inputs[3]);
            let parent = mux(&mut aig, inputs[0], child.not_if(negate_branch), inputs[4]);
            aig.bads.push(parent);
            let (cnf, map) = aig.cnf_compact();
            assert!(map[*child.var()].is_constant());
            assert_eq!(cnf.num_clause(), 7); // constant clause and six ITE clauses
            assert!(cnf.clause().all(|clause| clause.len() <= 4));
            check_truth_table(&aig, &cnf, &map);
        }
    }

    #[test]
    fn inline_both_ite_branches() {
        let mut aig = Aig::new();
        let inputs: Vec<_> = (0..7).map(|_| AigEdge::from(aig.new_input())).collect();
        let left = mux(&mut aig, inputs[1], inputs[2], inputs[3]);
        let right = mux(&mut aig, inputs[4], inputs[5], inputs[6]);
        let parent = mux(&mut aig, inputs[0], left, !right);
        aig.bads.push(parent);
        let (cnf, map) = aig.cnf_compact();
        assert!(map[*left.var()].is_constant());
        assert!(map[*right.var()].is_constant());
        assert_eq!(cnf.num_clause(), 9);
        assert!(cnf.clause().all(|clause| clause.len() <= 4));
        check_truth_table(&aig, &cnf, &map);
    }

    #[test]
    fn keep_externally_used_ite() {
        let mut aig = Aig::new();
        let inputs: Vec<_> = (0..5).map(|_| AigEdge::from(aig.new_input())).collect();
        let child = mux(&mut aig, inputs[1], inputs[2], inputs[3]);
        let parent = mux(&mut aig, inputs[0], child, inputs[4]);
        aig.bads.extend([parent, child]);
        let (cnf, map) = aig.cnf_compact();
        assert!(!map[*child.var()].is_constant());
        check_truth_table(&aig, &cnf, &map);
    }

    #[test]
    fn limit_inlining_to_one_level() {
        let mut aig = Aig::new();
        let inputs: Vec<_> = (0..7).map(|_| AigEdge::from(aig.new_input())).collect();
        let inner = mux(&mut aig, inputs[2], inputs[3], inputs[4]);
        let middle = mux(&mut aig, inputs[1], inner, inputs[5]);
        let outer = mux(&mut aig, inputs[0], middle, inputs[6]);
        aig.bads.push(outer);
        let (cnf, map) = aig.cnf_compact();
        assert!(map[*middle.var()].is_constant());
        assert!(!map[*inner.var()].is_constant());
        assert!(cnf.clause().all(|clause| clause.len() <= 4));
        check_truth_table(&aig, &cnf, &map);
    }
}
