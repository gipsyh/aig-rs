use crate::{Aig, AigEdge, AigLatch, AigNode, AigNodeId};
use libc::{fopen, FILE};
use logic_form::Lit;
use std::{
    ffi::{c_char, CString},
    os::raw::c_void,
    slice::from_raw_parts,
};

extern "C" {
    fn aiger_init() -> *mut c_void;
    fn aiger_read_from_file(aiger: *mut c_void, file: *mut FILE) -> *mut c_char;
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

    pub fn from_file(file: &str) -> Self {
        let file = CString::new(file).unwrap();
        let mode = CString::new("r").unwrap();
        let file = unsafe { fopen(file.as_ptr(), mode.as_ptr()) };
        let aiger = unsafe { aiger_init() };
        if !unsafe { aiger_read_from_file(aiger, file) }.is_null() {
            println!("read aiger failed.");
            panic!();
        }
        let aiger = unsafe { &mut *(aiger as *mut Aiger) };
        let node_len = (aiger.num_inputs + aiger.num_latches + aiger.num_ands + 1) as usize;
        let mut nodes: Vec<AigNode> = Vec::with_capacity(node_len);
        let nodes_remaining = nodes.spare_capacity_mut();
        nodes_remaining[0].write(AigNode::new_false(0));
        let inputs: Vec<AigNodeId> =
            unsafe { from_raw_parts(aiger.inputs, aiger.num_inputs as usize) }
                .iter()
                .map(|l| l.lit.var().into())
                .collect();
        let mut latchs = Vec::new();
        for i in 0..aiger.num_latches {
            let l = unsafe { &*aiger.latches.add(i as usize) };
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
            .into_iter()
            .map(|i| unsafe { *aiger.outputs.add(i as usize) })
            .map(|l| AigEdge::from_lit(l.lit))
            .collect();
        let bads: Vec<AigEdge> = unsafe { from_raw_parts(aiger.bad, aiger.num_bad as usize) }
            .iter()
            .map(|l| AigEdge::from_lit(l.lit))
            .collect();
        let constraints: Vec<AigEdge> =
            unsafe { from_raw_parts(aiger.constraints, aiger.num_constraints as usize) }
                .iter()
                .map(|l| AigEdge::from_lit(l.lit))
                .collect();
        for i in inputs.iter() {
            nodes_remaining[*i].write(AigNode::new_input(*i));
        }
        for l in latchs.iter() {
            nodes_remaining[l.input].write(AigNode::new_input(l.input));
        }
        let ands = unsafe { from_raw_parts(aiger.ands, aiger.num_ands as usize) };
        for a in ands {
            let id: usize = a.lhs.var().into();
            nodes_remaining[id].write(AigNode::new_and(
                id,
                AigEdge::from_lit(a.rhs0),
                AigEdge::from_lit(a.rhs1),
            ));
        }
        unsafe { nodes.set_len(node_len) };
        Self {
            nodes,
            inputs,
            latchs,
            outputs,
            bads,
            constraints,
            latch_group: Default::default(),
        }
    }
}
