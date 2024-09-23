use crate::{Aig, AigEdge};
use logic_form::{Clause, Cube, Lemma, Lit, Var};
use std::{
    collections::{HashMap, HashSet},
    ops::{Deref, DerefMut},
};

#[derive(Default, Clone, Debug)]
pub struct NodeCnfContext {
    pub deps: HashSet<usize>,
    pub outs: HashSet<usize>,
    pub cnf: Vec<Clause>,
}

impl NodeCnfContext {
    #[inline]
    fn filter(&self, f: usize) -> (Vec<Clause>, Vec<Clause>) {
        let mut pos = Vec::new();
        let mut neg = Vec::new();
        let f = Var::new(f).lit();
        for cls in self.cnf.iter() {
            if let Some(l) = cls.iter().find(|l| l.var() == f.var()) {
                if *l == f {
                    pos.push(cls.clone());
                } else {
                    neg.push(cls.clone());
                }
            }
        }
        (pos, neg)
    }

    fn remove(&mut self, f: usize) {
        self.deps.retain(|d| *d != f);
        self.outs.retain(|d| *d != f);
        let f = Var::new(f);
        self.cnf.retain(|cls| cls.iter().all(|l| l.var() != f));
    }

    fn clear(&mut self) {
        self.deps.clear();
        self.outs.clear();
        self.cnf.clear();
    }

    fn simplify(&mut self) {
        self.cnf = clause_subsume_simplify(self.cnf.clone());
    }
}

pub struct AigCnfContext {
    ctx: Vec<NodeCnfContext>,
}

impl AigCnfContext {
    fn new(num: usize) -> Self {
        let mut ctx = vec![NodeCnfContext::default(); num];
        ctx[0].cnf.push(Clause::from([Lit::constant_lit(true)]));
        Self { ctx }
    }

    #[inline]
    pub fn cnf(&self) -> Vec<Clause> {
        let mut res = Vec::new();
        for c in self.iter() {
            res.extend_from_slice(&c.cnf);
        }
        res
    }

    fn cost(&self, n: usize) -> usize {
        let nv = Var::new(n);
        let res: usize = self[n]
            .outs
            .iter()
            .map(|o| {
                self[*o]
                    .cnf
                    .iter()
                    .filter(|cls| cls.iter().any(|l| l.var() == nv))
                    .count()
            })
            .sum();
        res + self[n].cnf.len()
    }

    fn add_node_cnf(&mut self, n: usize, cnf: &[Clause]) {
        self.ctx[n].cnf.extend_from_slice(cnf);
        let mut deps = HashSet::new();
        for cls in cnf.iter() {
            for l in cls.iter() {
                let v: usize = l.var().into();
                if v != n {
                    deps.insert(v);
                }
            }
        }
        for d in deps.iter() {
            self.ctx[*d].outs.insert(n);
        }
        self.ctx[n].deps.extend(deps);
    }

    fn resolvent_of_one_fanout(&mut self, n: usize, o: usize) -> Vec<Clause> {
        let mut res = Vec::new();
        let (pos, neg) = self[n].filter(n);
        let (op, on) = self[o].filter(n);
        let pivot = Var::new(n);
        res.extend(resolvent(&pos, &on, pivot));
        res.extend(resolvent(&op, &neg, pivot));
        clause_subsume_simplify(res)
    }

    fn eliminate(&mut self, n: usize) -> bool {
        let origin_cost = self.cost(n);
        let mut o_resolvent = Vec::new();
        let mut outs = Vec::from_iter(self[n].outs.clone());
        outs.sort();
        for o in outs.iter() {
            o_resolvent.push(self.resolvent_of_one_fanout(n, *o));
        }
        let new_cost = o_resolvent.iter().map(|cls| cls.len()).sum::<usize>();
        if new_cost > origin_cost {
            return false;
        }
        for d in self[n].deps.clone() {
            self.ctx[d].remove(n);
        }
        self.ctx[n].clear();
        for (o, or) in outs.iter().zip(o_resolvent.iter()) {
            self.ctx[*o].remove(n);
            self.add_node_cnf(*o, &or);
            self.ctx[*o].simplify();
        }
        true
    }
}

impl Deref for AigCnfContext {
    type Target = [NodeCnfContext];

    #[inline]
    fn deref(&self) -> &Self::Target {
        &self.ctx
    }
}

impl DerefMut for AigCnfContext {
    #[inline]
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.ctx
    }
}

fn resolvent(pcnf: &[Clause], ncnf: &[Clause], pivot: Var) -> Vec<Clause> {
    let mut res = Vec::new();
    for pcls in pcnf.iter() {
        for ncls in ncnf.iter() {
            let resolvent = pcls.resolvent(ncls, pivot);
            if !resolvent.is_empty() {
                res.push(resolvent);
            }
        }
    }
    res
}

fn clause_subsume_simplify(lemmas: Vec<Clause>) -> Vec<Clause> {
    let mut lemmas: Vec<Lemma> = lemmas
        .iter()
        .map(|cls| Lemma::new(Cube::from(cls.as_slice())))
        .collect();
    lemmas.sort_by_key(|l| l.len());
    let mut i = 0;
    while i < lemmas.len() {
        if lemmas[i].is_empty() {
            i += 1;
            continue;
        }
        let mut update = false;
        for j in 0..lemmas.len() {
            if i == j {
                continue;
            }
            if lemmas[j].is_empty() {
                continue;
            }
            let (res, diff) = lemmas[i].subsume_execpt_one(&lemmas[j]);
            if res {
                lemmas[j] = Default::default();
                continue;
            } else if let Some(diff) = diff {
                if lemmas[i].len() == lemmas[j].len() {
                    update = true;
                    let mut cube = lemmas[i].cube().clone();
                    cube.retain(|l| *l != diff);
                    assert!(cube.len() + 1 == lemmas[i].len());
                    lemmas[i] = Lemma::new(cube);
                    lemmas[j] = Default::default();
                } else {
                    let mut cube = lemmas[j].cube().clone();
                    cube.retain(|l| *l != !diff);
                    assert!(cube.len() + 1 == lemmas[j].len());
                    lemmas[j] = Lemma::new(cube);
                }
            }
        }
        if !update {
            i += 1;
        }
    }
    lemmas.retain(|l| !l.is_empty());
    lemmas
        .into_iter()
        .map(|l| Clause::from(l.cube().as_slice()))
        .collect()
}

impl Aig {
    #[inline]
    fn get_root_refs(&self) -> HashSet<usize> {
        let mut refs = HashSet::new();
        for l in self.latchs.iter() {
            refs.insert(l.next.node_id());
        }
        for l in self
            .constraints
            .iter()
            .chain(self.bads.iter())
            .chain(self.outputs.iter())
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

    pub fn get_cnf(&self) -> Vec<Clause> {
        let mut refs = self.get_root_refs();
        let mut ans = Vec::new();
        ans.push(Clause::from([Lit::constant_lit(true)]));
        for i in self.nodes_range().rev() {
            if self.nodes[i].is_and() && (refs.contains(&i)) {
                let n = Var::new(self.nodes[i].node_id()).lit();
                if let Some((xor0, xor1)) = self.is_xor(i) {
                    refs.insert(xor0.node_id());
                    refs.insert(xor1.node_id());
                    let xor0 = xor0.to_lit();
                    let xor1 = xor1.to_lit();
                    ans.push(Clause::from([!xor0, xor1, n]));
                    ans.push(Clause::from([xor0, !xor1, n]));
                    ans.push(Clause::from([xor0, xor1, !n]));
                    ans.push(Clause::from([!xor0, !xor1, !n]));
                } else if let Some((c, t, e)) = self.is_ite(i) {
                    refs.insert(c.node_id());
                    refs.insert(t.node_id());
                    refs.insert(e.node_id());
                    let c = c.to_lit();
                    let t = t.to_lit();
                    let e = e.to_lit();
                    ans.push(Clause::from([t, !c, !n]));
                    ans.push(Clause::from([!t, !c, n]));
                    ans.push(Clause::from([e, c, !n]));
                    ans.push(Clause::from([!e, c, n]));
                } else {
                    refs.insert(self.nodes[i].fanin0().id);
                    refs.insert(self.nodes[i].fanin1().id);
                    let fanin0 = self.nodes[i].fanin0().to_lit();
                    let fanin1 = self.nodes[i].fanin1().to_lit();
                    ans.push(Clause::from([!n, fanin0]));
                    ans.push(Clause::from([!n, fanin1]));
                    ans.push(Clause::from([n, !fanin0, !fanin1]));
                }
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

    pub fn get_cnf_context(&self) -> AigCnfContext {
        let mut refs = self.get_root_refs();
        let mut ctx = AigCnfContext::new(self.num_nodes());
        for i in self.nodes_range().rev() {
            if self.nodes[i].is_and() && (refs.contains(&i)) {
                let n = Var::new(self.nodes[i].node_id()).lit();
                if let Some((xor0, xor1)) = self.is_xor(i) {
                    refs.insert(xor0.node_id());
                    refs.insert(xor1.node_id());
                    let xor0 = xor0.to_lit();
                    let xor1 = xor1.to_lit();
                    let mut cnf = Vec::new();
                    cnf.push(Clause::from([!xor0, xor1, n]));
                    cnf.push(Clause::from([xor0, !xor1, n]));
                    cnf.push(Clause::from([xor0, xor1, !n]));
                    cnf.push(Clause::from([!xor0, !xor1, !n]));
                    ctx.add_node_cnf(n.var().into(), &cnf);
                } else if let Some((c, t, e)) = self.is_ite(i) {
                    refs.insert(c.node_id());
                    refs.insert(t.node_id());
                    refs.insert(e.node_id());
                    let c = c.to_lit();
                    let t = t.to_lit();
                    let e = e.to_lit();
                    let mut cnf = Vec::new();
                    cnf.push(Clause::from([t, !c, !n]));
                    cnf.push(Clause::from([!t, !c, n]));
                    cnf.push(Clause::from([e, c, !n]));
                    cnf.push(Clause::from([!e, c, n]));
                    ctx.add_node_cnf(n.var().into(), &cnf);
                } else {
                    refs.insert(self.nodes[i].fanin0().id);
                    refs.insert(self.nodes[i].fanin1().id);
                    let fanin0 = self.nodes[i].fanin0().to_lit();
                    let fanin1 = self.nodes[i].fanin1().to_lit();
                    let mut cnf = Vec::new();
                    cnf.push(Clause::from([!n, fanin0]));
                    cnf.push(Clause::from([!n, fanin1]));
                    cnf.push(Clause::from([n, !fanin0, !fanin1]));
                    ctx.add_node_cnf(n.var().into(), &cnf);
                }
            }
        }
        ctx
    }

    pub fn get_simplified_cnf_context(&self) -> AigCnfContext {
        let mut ctx = self.get_cnf_context();
        let mut frozen = HashSet::new();
        for i in self.inputs.iter() {
            frozen.insert(*i);
        }
        for l in self.latchs.iter() {
            frozen.insert(l.input);
            frozen.insert(l.next.node_id());
        }
        for l in self
            .constraints
            .iter()
            .chain(self.outputs.iter())
            .chain(self.bads.iter())
        {
            frozen.insert(l.node_id());
        }
        for _ in 0.. {
            let mut update = false;
            for i in self.nodes_range().filter(|l| !frozen.contains(l)) {
                if ctx[i].outs.len() > 0 {
                    if ctx.eliminate(i) {
                        update = true;
                    }
                }
            }
            if !update {
                break;
            }
        }
        for i in self.nodes_range().filter(|l| !frozen.contains(l)) {
            ctx[i].simplify();
        }
        ctx
    }
}
