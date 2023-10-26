use crate::{Aig, AigEdge, AigNodeId};
use logic_form::{Clause, Cnf, Lit};
use std::collections::HashSet;

impl Aig {
    pub fn get_optimized_cnf(&self, logic: &[AigEdge]) -> Cnf {
        let mut refs = HashSet::new();
        for l in logic {
            refs.insert(*l);
        }
        let mut ans = Cnf::new();
        for i in self.nodes_range().rev() {
            let edge: AigEdge = self.nodes[i].node_id().into();
            if self.nodes[i].is_and() && (refs.contains(&edge) || refs.contains(&!edge)) {
                refs.insert(self.nodes[i].fanin0());
                refs.insert(self.nodes[i].fanin1());
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
                refs.insert(!self.nodes[i].fanin0());
                refs.insert(!self.nodes[i].fanin1());
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

    pub fn get_cnf(&self) -> Cnf {
        let mut ans = Cnf::new();
        for i in self.nodes_range() {
            if self.nodes[i].is_and() {
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
        for c in self.constraints.iter() {
            ans.push(Clause::from([c.to_lit()]));
        }
        ans
    }

    fn rec_get_block(
        &self,
        node: AigNodeId,
        block: &mut Vec<AigEdge>,
        visit: &mut HashSet<AigNodeId>,
    ) {
        if visit.contains(&node) {
            return;
        }
        visit.insert(node);
        if self.nodes[node].is_and() {
            let mut closure = |fanin: AigEdge| {
                if fanin.compl() {
                    if !visit.contains(&fanin.node_id()) {
                        visit.insert(fanin.node_id());
                        block.push(fanin);
                    }
                } else {
                    self.rec_get_block(fanin.node_id(), block, visit);
                }
            };
            closure(self.nodes[node].fanin0());
            closure(self.nodes[node].fanin1());
        } else {
            block.push(node.into());
        }
    }

    fn rec_get_block_cnf(&self, node: AigNodeId, visit: &mut HashSet<AigNodeId>, cnf: &mut Cnf) {
        if visit.contains(&node) {
            return;
        }
        visit.insert(node);
        if !self.nodes[node].is_and() {
            return;
        }
        let mut block = Vec::new();
        self.rec_get_block(node, &mut block, &mut HashSet::new());
        let node_lit = AigEdge::new(node, false).to_lit();
        let mut clause = Clause::from([node_lit]);
        for block_node in block {
            self.rec_get_block_cnf(block_node.node_id(), visit, cnf);
            let block_node = block_node.to_lit();
            cnf.push(Clause::from([!node_lit, block_node]));
            clause.push(!block_node);
        }
        cnf.push(clause);
    }

    pub fn get_block_optimized_cnf(&self) -> Cnf {
        let mut cnf = Cnf::new();
        let mut visit = HashSet::new();
        for l in self.latchs.iter() {
            self.rec_get_block_cnf(l.next.node_id(), &mut visit, &mut cnf);
        }
        for bad in self.bads.iter() {
            self.rec_get_block_cnf(bad.node_id(), &mut visit, &mut cnf);
        }
        cnf
    }
}
