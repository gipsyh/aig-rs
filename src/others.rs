use crate::{Aig, AigEdge, AigNodeType};
use giputils::{
    gvec::Gvec,
    hash::{GHashMap, GHashSet},
};
use logicrs::{Var, VarVMap};
use std::mem::take;

impl Aig {
    pub fn coi(&self, root: &[Var]) -> GHashSet<Var> {
        let mut latchs = GHashMap::new();
        for l in self.latchs.iter() {
            latchs.insert(l.input, *l);
        }
        let mut refine = GHashSet::new();
        refine.insert(Var::CONST);
        let mut queue = Vec::new();
        for r in root {
            if !refine.contains(r) {
                queue.push(*r);
                refine.insert(*r);
            }
        }
        while let Some(n) = queue.pop() {
            let mut refine_insert = |v: Var| {
                if !refine.contains(&v) {
                    queue.push(v);
                    refine.insert(v);
                }
            };
            if self.nodes[*n].is_and() {
                let fanin0 = self.nodes[*n].fanin0();
                let fanin1 = self.nodes[*n].fanin1();
                refine_insert(fanin0.var());
                refine_insert(fanin1.var());
            } else if let Some(l) = latchs.get(&n) {
                refine_insert(l.next.var());
            }
        }
        refine
    }

    pub fn coi_refine(&self) -> (Aig, VarVMap) {
        let mut refine_root: Vec<Var> = self
            .constraints
            .iter()
            .chain(self.outputs.iter())
            .chain(self.bads.iter())
            .chain(self.justice.iter().flatten())
            .chain(self.fairness.iter())
            .map(|e| e.var())
            .collect();
        for l in self.latchs.iter() {
            if let Some(init) = l.init
                && !init.is_const()
            {
                refine_root.push(init.var());
                refine_root.push(l.input);
            }
            refine_root.push(l.input);
        }
        if !self.justice.is_empty() || !self.fairness.is_empty() {
            refine_root.extend(self.latchs.iter().map(|e| e.input));
        }
        let refine = self.coi(&refine_root);
        let mut refine = Vec::from_iter(refine);
        refine.sort();
        let mut refine_map: GHashMap<Var, Var> = GHashMap::new();
        for (i, r) in refine.iter().enumerate() {
            refine_map.insert(*r, Var::new(i));
        }
        let edge_map = |e: AigEdge| e.map(&|v| refine_map[&v]);
        let mut nodes = Gvec::new();
        let mut restore = VarVMap::new();
        for (id, n) in self.nodes.iter().enumerate() {
            if let Some(new_id) = refine_map.get(&Var::new(id)) {
                restore.insert(*new_id, Var::new(id));
                let mut new_node = n.clone();
                if let AigNodeType::And(fanin0, fanin1) = &mut new_node.typ {
                    *fanin0 = edge_map(*fanin0);
                    *fanin1 = edge_map(*fanin1);
                }
                nodes.push(new_node);
            }
        }
        let inputs: Vec<Var> = self
            .inputs
            .iter()
            .filter_map(|n| refine_map.get(n).copied())
            .collect();
        let mut latchs = Vec::new();
        for l in self.latchs.iter() {
            if let Some(new_input) = refine_map.get(&l.input) {
                let mut new_latch = *l;
                new_latch.input = *new_input;
                new_latch.next = edge_map(new_latch.next);
                if let Some(init) = &mut new_latch.init {
                    *init = edge_map(*init);
                }
                latchs.push(new_latch);
            }
        }
        let outputs: Vec<AigEdge> = self.outputs.iter().map(|n| edge_map(*n)).collect();
        let bads: Vec<AigEdge> = self.bads.iter().map(|n| edge_map(*n)).collect();
        let constraints: Vec<AigEdge> = self.constraints.iter().map(|n| edge_map(*n)).collect();
        let justice: Vec<Vec<AigEdge>> = self
            .justice
            .iter()
            .map(|j| j.iter().map(|n| edge_map(*n)).collect())
            .collect();
        let fairness: Vec<AigEdge> = self.fairness.iter().map(|n| edge_map(*n)).collect();
        let mut symbols = GHashMap::new();
        for (k, s) in self.symbols.iter() {
            if let Some(r) = refine_map.get(k) {
                symbols.insert(*r, s.clone());
            }
        }
        (
            Self {
                nodes,
                inputs,
                latchs,
                outputs,
                bads,
                constraints,
                symbols,
                justice,
                fairness,
            },
            restore,
        )
    }

    pub fn unroll(&mut self, from: &Aig) {
        let mut next_map = GHashMap::new();
        let false_edge = AigEdge::constant(false);
        next_map.insert(false_edge.var(), false_edge);
        for l in self.latchs.iter() {
            next_map.insert(l.input, l.next);
        }
        for i in from.nodes_range() {
            let v = Var::new(i);
            if next_map.contains_key(&v) {
                continue;
            }
            if from.nodes[i].is_and() {
                let fanin0 = self.nodes[i].fanin0();
                let fanin1 = self.nodes[i].fanin1();
                let fanin0 = next_map[&fanin0.var()].not_if(fanin0.compl());
                let fanin1 = next_map[&fanin1.var()].not_if(fanin1.compl());
                let next = self.new_and_node(fanin0, fanin1);
                next_map.insert(v, next);
            } else {
                let input = self.new_leaf_node();
                self.inputs.push(input);
                let next: AigEdge = input.into();
                next_map.insert(v, next);
            }
        }
        let edge_map = |e: AigEdge| next_map[&e.var()].not_if(e.compl());
        for (f, s) in from.latchs.iter().zip(self.latchs.iter_mut()) {
            s.next = edge_map(f.next);
        }
        for o in from.outputs.clone() {
            self.outputs.push(edge_map(o));
        }
        for b in from.bads.clone() {
            self.bads.push(edge_map(b));
        }
        for c in from.constraints.clone() {
            self.constraints.push(edge_map(c));
        }
        for j in from.justice.iter() {
            self.justice.push(j.iter().map(|e| edge_map(*e)).collect());
        }
        for f in from.fairness.clone() {
            self.fairness.push(edge_map(f));
        }
    }

    pub fn unroll_to(&self, k: usize) -> Aig {
        let mut res = self.clone();
        for _ in 0..k {
            res.unroll(self);
        }
        res
    }

    pub fn merge(&mut self, other: &Aig) {
        let offset = self.num_nodes() - 1;
        let map = |v: Var| {
            if v.is_constant() {
                v
            } else {
                Var::new(usize::from(v) + offset)
            }
        };
        for i in 1..other.num_nodes() {
            let n = other.nodes[i].map(&map);
            self.nodes.push(n);
        }
        for i in other.inputs.iter() {
            self.inputs.push(map(*i));
        }
        for l in other.latchs.iter() {
            let mut l = *l;
            l.input = map(l.input);
            l.next = l.next.map(&map);
            self.latchs.push(l);
        }
        for l in other.outputs.iter() {
            self.outputs.push(l.map(&map));
        }
        for l in other.bads.iter() {
            self.bads.push(l.map(&map));
        }
        for l in other.constraints.iter() {
            self.constraints.push(l.map(&map));
        }
        for j in other.justice.iter() {
            self.justice.push(j.iter().map(|e| e.map(&map)).collect());
        }
        for l in other.fairness.iter() {
            self.fairness.push(l.map(&map));
        }
    }

    pub fn reencode(&self) -> Self {
        let mut res = Self::new();
        let mut encode_map = Gvec::new();
        encode_map.reserve(self.nodes.len());
        let mut max_id = 0;
        for &l in self.inputs.iter() {
            max_id += 1;
            encode_map[*l] = Var::new(max_id);
        }
        for l in self.latchs.iter() {
            max_id += 1;
            encode_map[*l.input] = Var::new(max_id);
        }
        for i in 0..self.nodes.len() {
            if self.nodes[i].is_and() {
                max_id += 1;
                encode_map[i] = Var::new(max_id);
            }
        }
        assert!(max_id + 1 == self.nodes.len());
        let edge_map = |e: AigEdge| e.map(&|v| encode_map[*v]);
        for &l in self.inputs.iter() {
            assert!(res.new_input() == encode_map[*l]);
        }
        for l in self.latchs.iter() {
            assert!(res.new_latch(edge_map(l.next), l.init) == encode_map[*l.input]);
        }
        for i in 1..self.nodes.len() {
            if self.nodes[i].is_and() {
                let fanin0 = edge_map(self.nodes[i].fanin0());
                let fanin1 = edge_map(self.nodes[i].fanin1());
                let nl = res.trivial_new_and_node(fanin0, fanin1).var();
                assert!(encode_map[i] == nl);
            }
        }
        res.outputs = self.outputs.iter().map(|e| edge_map(*e)).collect();
        res.bads = self.bads.iter().map(|e| edge_map(*e)).collect();
        res.constraints = self.constraints.iter().map(|e| edge_map(*e)).collect();
        res.justice = self
            .justice
            .iter()
            .map(|j| j.iter().map(|e| edge_map(*e)).collect())
            .collect();
        res.fairness = self.fairness.iter().map(|e| edge_map(*e)).collect();
        res.symbols = self
            .symbols
            .iter()
            .map(|(&v, s)| (encode_map[*v], s.clone()))
            .collect();
        assert!(res.nodes.len() == self.nodes.len());
        res
    }

    pub fn aig_move(&self) -> Self {
        let mut res = self.clone();
        let latch = res.new_leaf_node();
        let constrains = res.new_ands_node(res.constraints.clone());
        let next = res.new_and_node(latch.into(), constrains);
        res.add_latch(latch, next, Some(AigEdge::constant(true)));
        if !res.bads.is_empty() {
            res.bads[0] = res.new_and_node(next, res.bads[0]);
        }
        if !res.outputs.is_empty() {
            res.outputs[0] = res.new_and_node(next, res.outputs[0]);
        }
        res.constraints.clear();
        res
    }

    pub fn compress_property(&mut self) -> Vec<AigEdge> {
        let b = take(&mut self.bads);
        let p = self.new_ors_node(b.clone());
        self.bads.push(p);
        b
    }

    pub fn gate_init_to_constraint(&mut self) {
        let mut gate_init = Vec::new();
        for l in self.latchs.iter_mut() {
            if let Some(init) = l.init
                && !init.is_const()
            {
                gate_init.push((l.input, init));
                l.init = None;
            }
        }
        if gate_init.is_empty() {
            return;
        }
        let init: AigEdge = self
            .new_latch(AigEdge::constant(false), Some(AigEdge::constant(true)))
            .into();
        for (l, gi) in gate_init {
            let l = AigEdge::from(l.lit());
            let eq = self.new_eq_node(l, gi);
            let init_eq = self.new_imply_node(init, eq);
            self.constraints.push(init_eq);
        }
    }
}
