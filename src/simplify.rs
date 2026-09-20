use crate::{Aig, AigEdge, AigNode};
use giputils::{gvec::Gvec, hash::GHashMap};
use logicrs::Var;

impl Aig {
    /// Simplify combinational logic without renumbering inputs or latches.
    /// Aliases (including complemented aliases) are propagated to all fanins
    /// and roots. Obsolete gates are left for reachability-based CNF encoding
    /// to discard; no sequential assumptions or constraints are used.
    pub fn simplify_combinational(&mut self) {
        let mut map: Gvec<AigEdge> = (0..self.num_nodes())
            .map(|i| AigEdge::from(Var(i)))
            .collect();
        let mut unique = GHashMap::new();
        for i in self.nodes_range() {
            if !self.nodes[i].is_and() {
                continue;
            }
            let (a, b) = self.nodes[i].fanin();
            let a = map[*a.var()].not_if(a.compl());
            let b = map[*b.var()].not_if(b.compl());
            let (a, b) = self.simplify_and_fanins(a, b);
            self.nodes[i] = AigNode::new_and(a, b);
            if a == b {
                map[i] = a;
                continue;
            }
            if let Some((_, t, e)) = self.is_ite(Var(i))
                && t == e
            {
                // ITE(c, t, t) = t, even when t is complemented.
                map[i] = t;
                continue;
            }
            let key = self.nodes[i].fanin();
            map[i] = *unique.entry(key).or_insert(AigEdge::from(Var(i)));
        }
        let remap = |e: &mut AigEdge| *e = map[*e.var()].not_if(e.compl());
        for latch in &mut self.latchs {
            remap(&mut latch.next);
            if let Some(init) = &mut latch.init {
                remap(init);
            }
        }
        for edge in self
            .outputs
            .iter_mut()
            .chain(self.bads.iter_mut())
            .chain(self.constraints.iter_mut())
            .chain(self.justice.iter_mut().flatten())
            .chain(self.fairness.iter_mut())
        {
            remap(edge);
        }
    }

    // Return (x, x) for an alias, otherwise a reduced pair of AND fanins.
    fn simplify_and_fanins(&self, mut a: AigEdge, mut b: AigEdge) -> (AigEdge, AigEdge) {
        loop {
            if a.is_constant(false) || b.is_constant(false) || a == !b {
                let f = AigEdge::constant(false);
                return (f, f);
            }
            if a.is_constant(true) || a == b {
                return (b, b);
            }
            if b.is_constant(true) {
                return (a, a);
            }
            let mut reduced = None;
            for (outer, inner) in [(a, b), (b, a)] {
                if !self.nodes[*inner.var()].is_and() {
                    continue;
                }
                let (x, y) = self.nodes[*inner.var()].fanin();
                if x == outer || y == outer {
                    if !inner.compl() {
                        return (inner, inner); // a & (a & b)
                    }
                    // a & !(a & b) = a & !b
                    reduced = Some((outer, !(if x == outer { y } else { x })));
                    break;
                }
                if x == !outer || y == !outer {
                    let result = if inner.compl() {
                        outer // a & !(!a & b)
                    } else {
                        AigEdge::constant(false) // a & (!a & b)
                    };
                    return (result, result);
                }
            }
            match reduced {
                Some(pair) => (a, b) = pair,
                None => return (a, b),
            }
        }
    }

    pub fn is_xor(&self, n: Var) -> Option<(AigEdge, AigEdge)> {
        if !self.nodes[*n].is_and() {
            return None;
        }
        let (fanin0, fanin1) = self.nodes[*n].fanin();
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
            return Some((fanin00, fanin01));
        }
        None
    }

    pub fn is_ite(&self, n: Var) -> Option<(AigEdge, AigEdge, AigEdge)> {
        if !self.nodes[*n].is_and() {
            return None;
        }
        let (fanin0, fanin1) = self.nodes[*n].fanin();
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
        Some((i, t, e))
    }
}
