use crate::{Aig, AigEdge, AigLatch, AigNode};
use libc::{fopen, FILE};
use logic_form::Lit;
use std::{
    collections::HashMap,
    ffi::{c_char, CStr, CString},
    os::raw::c_void,
    ptr::null,
};

extern "C" {
    fn aiger_init() -> *mut c_void;
    fn aiger_reset(aiger: *mut c_void);
    fn aiger_read_from_file(aiger: *mut c_void, file: *mut FILE) -> *mut c_char;
    fn aiger_add_input(aiger: *mut c_void, lit: u32, s: *const c_char);
    fn aiger_add_latch(aiger: *mut c_void, lit: u32, next: u32, s: *const c_char);
    fn aiger_add_output(aiger: *mut c_void, lit: u32, s: *const c_char);
    fn aiger_add_bad(aiger: *mut c_void, lit: u32, s: *const c_char);
    fn aiger_add_constraint(aiger: *mut c_void, lit: u32, s: *const c_char);
    fn aiger_add_and(aiger: *mut c_void, lhs: u32, rhs0: u32, rhs1: u32);
    fn aiger_add_reset(aiger: *mut c_void, lit: u32, reset: u32);
    fn aiger_open_and_write_to_file(aiger: *mut c_void, file: *const c_char) -> i32;
}

#[repr(C)]
struct Aiger {
    maxvar: u32,
    num_inputs: u32,
    num_latches: u32,
    num_outputs: u32,
    num_ands: u32,
    num_bad: u32,
    num_constraints: u32,
    num_justice: u32,
    num_fairness: u32,

    // [0..num_inputs[
    inputs: *mut AigerSymbol,
    // [0..num_latches[
    latches: *mut AigerSymbol,
    // [0..num_outputs[
    outputs: *mut AigerSymbol,
    // [0..num_bad[
    bad: *mut AigerSymbol,
    // [0..num_constraints[
    constraints: *mut AigerSymbol,
    // [0..num_justice[
    justice: *mut AigerSymbol,
    // [0..num_fairness[
    fairness: *mut AigerSymbol,
    ands: *mut AigerAnd,
    comments: *mut *mut c_char,
}

#[repr(C)]
#[derive(Clone, Copy)]
struct AigerSymbol {
    lit: Lit,
    next: Lit,
    reset: u32,
    size: u32,
    lits: *mut u32,
    name: *mut c_char,
}

#[repr(C)]
struct AigerAnd {
    lhs: Lit,
    rhs0: Lit,
    rhs1: Lit,
}

impl Aig {
    // fn setup_fanouts(&mut self) {
    //     for id in self.nodes_range() {
    //         if self.nodes[id].is_and() {
    //             let fanin0 = self.nodes[id].fanin0();
    //             let compl = fanin0.compl();
    //             self.nodes[fanin0.node_id()]
    //                 .fanouts
    //                 .push(AigEdge::new(id, compl));
    //             let fanin1 = self.nodes[id].fanin1();
    //             let compl = fanin1.compl();
    //             self.nodes[fanin1.node_id()]
    //                 .fanouts
    //                 .push(AigEdge::new(id, compl));
    //         }
    //     }
    // }

    pub fn from_file(f: &str) -> Self {
        let file = CString::new(f).unwrap();
        let mode = CString::new("r").unwrap();
        let file = unsafe { fopen(file.as_ptr(), mode.as_ptr()) };
        if file.is_null() {
            panic!("error: {f} not found.");
        }
        let aiger = unsafe { aiger_init() };
        if !unsafe { aiger_read_from_file(aiger, file) }.is_null() {
            panic!("error: read {f} failed.");
        }
        let aiger = unsafe { &mut *(aiger as *mut Aiger) };
        let node_len = (aiger.num_inputs + aiger.num_latches + aiger.num_ands + 1) as usize;
        let mut nodes: Vec<AigNode> = Vec::with_capacity(node_len);
        let nodes_remaining = nodes.spare_capacity_mut();
        nodes_remaining[0].write(AigNode {
            id: 0,
            typ: crate::AigNodeType::False,
        });
        let inputs: Vec<usize> = (0..aiger.num_inputs)
            .map(|i| unsafe { *aiger.inputs.add(i as usize) })
            .map(|l| l.lit.var().into())
            .collect();
        let mut latchs = Vec::new();
        let mut group: HashMap<String, u32> = HashMap::new();
        let mut latch_group: HashMap<usize, u32> = HashMap::new();
        for i in 0..aiger.num_latches {
            let l = unsafe { &*aiger.latches.add(i as usize) };
            if !l.name.is_null() {
                let symbol = unsafe { CStr::from_ptr(l.name) };
                let symbol = symbol.to_str().unwrap();
                let symbol = if symbol.ends_with(']') {
                    let b = symbol.rfind('[').unwrap();
                    symbol[0..b].to_string()
                } else {
                    symbol.to_string()
                };
                if let Some(g) = group.get(&symbol) {
                    latch_group.insert(l.lit.var().into(), *g);
                } else {
                    let g = group.len() as u32;
                    group.insert(symbol, g);
                    latch_group.insert(l.lit.var().into(), g);
                }
            }
            let init = if l.reset <= 1 {
                Some(l.reset != 0)
            } else if l.reset == l.lit.into() {
                None
            } else {
                panic!()
            };
            latchs.push(AigLatch::new(
                l.lit.var().into(),
                AigEdge::from_lit(l.next),
                init,
            ));
        }
        let outputs: Vec<AigEdge> = (0..aiger.num_outputs)
            .map(|i| unsafe { *aiger.outputs.add(i as usize) })
            .map(|l| AigEdge::from_lit(l.lit))
            .collect();
        let bads: Vec<AigEdge> = (0..aiger.num_bad)
            .map(|i| unsafe { *aiger.bad.add(i as usize) })
            .map(|l| AigEdge::from_lit(l.lit))
            .collect();
        let constraints: Vec<AigEdge> = (0..aiger.num_constraints)
            .map(|i| unsafe { *aiger.constraints.add(i as usize) })
            .map(|l| AigEdge::from_lit(l.lit))
            .collect();
        for i in inputs.iter() {
            nodes_remaining[*i].write(AigNode {
                id: *i,
                typ: crate::AigNodeType::Leaf,
            });
        }
        for l in latchs.iter() {
            nodes_remaining[l.input].write(AigNode {
                id: l.input,
                typ: crate::AigNodeType::Leaf,
            });
        }
        for i in 0..aiger.num_ands {
            let a = unsafe { &*aiger.ands.add(i as usize) };
            let id: usize = a.lhs.var().into();
            nodes_remaining[id].write(AigNode::new_and(
                id,
                AigEdge::from_lit(a.rhs0),
                AigEdge::from_lit(a.rhs1),
            ));
        }
        unsafe { nodes.set_len(node_len) };
        unsafe { aiger_reset(aiger as *mut Aiger as *mut _) };
        Self {
            nodes,
            inputs,
            latchs,
            outputs,
            bads,
            constraints,
            latch_group,
        }
    }

    pub fn to_file(&self, f: &str) {
        let aiger = unsafe { aiger_init() };
        for i in self.nodes_range() {
            if self.nodes[i].is_and() {
                let fanin0 = self.nodes[i].fanin0().to_lit();
                let fanin1 = self.nodes[i].fanin1().to_lit();
                unsafe {
                    aiger_add_and(
                        aiger,
                        AigEdge::from(self.nodes[i].id).to_lit().into(),
                        fanin1.into(),
                        fanin0.into(),
                    )
                };
            };
        }
        for i in self.inputs.iter() {
            unsafe {
                aiger_add_input(
                    aiger,
                    AigEdge::from(self.nodes[*i].id).to_lit().into(),
                    null() as _,
                )
            };
        }
        for l in self.latchs.iter() {
            let lit = AigEdge::from(self.nodes[l.input].id).to_lit();
            unsafe { aiger_add_latch(aiger, lit.into(), l.next.to_lit().into(), null() as _) };
            let reset: u32 = if let Some(i) = l.init {
                i.into()
            } else {
                lit.into()
            };
            unsafe { aiger_add_reset(aiger, lit.into(), reset) };
        }
        for l in self.outputs.iter() {
            unsafe { aiger_add_output(aiger, l.to_lit().into(), null() as _) };
        }
        for l in self.bads.iter() {
            unsafe { aiger_add_bad(aiger, l.to_lit().into(), null() as _) };
        }
        for l in self.constraints.iter() {
            unsafe { aiger_add_constraint(aiger, l.to_lit().into(), null() as _) };
        }
        let file = CString::new(f).unwrap();
        let res = unsafe { aiger_open_and_write_to_file(aiger, file.as_ptr()) };
        assert!(res > 0, "write aig to {f} failed");
    }
}
