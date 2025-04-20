use crate::{Aig, AigEdge, AigLatch, AigNode};
use giputils::hash::GHashMap;
use libc::{FILE, fclose, fopen};
use logic_form::Lit;
use std::{
    ffi::{CStr, CString, c_char, c_void},
    path::Path,
    ptr::null,
};

unsafe extern "C" {
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
    fn aiger_write_to_file(aiger: *mut c_void, mode: i32, file: *mut FILE) -> i32;
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
    pub fn from_aiger(aiger: *mut c_void) -> Self {
        let aiger = unsafe { &mut *(aiger as *mut Aiger) };
        let node_len = (aiger.num_inputs + aiger.num_latches + aiger.num_ands + 1) as usize;
        let mut nodes: Vec<AigNode> = Vec::with_capacity(node_len);
        let nodes_remaining = nodes.spare_capacity_mut();
        nodes_remaining[0].write(AigNode {
            id: 0,
            typ: crate::AigNodeType::False,
        });
        let mut symbols = GHashMap::default();
        let inputs: Vec<usize> = (0..aiger.num_inputs)
            .map(|i| unsafe { *aiger.inputs.add(i as usize) })
            .map(|l| {
                let id: usize = l.lit.var().into();
                if !l.name.is_null() {
                    let symbol = unsafe { CStr::from_ptr(l.name) };
                    let symbol = symbol.to_str().unwrap();
                    symbols.insert(id, symbol.to_string());
                }
                id
            })
            .collect();
        let mut latchs = Vec::new();
        for i in 0..aiger.num_latches {
            let l = unsafe { &*aiger.latches.add(i as usize) };
            let id: usize = l.lit.var().into();
            if !l.name.is_null() {
                let symbol = unsafe { CStr::from_ptr(l.name) };
                let symbol = symbol.to_str().unwrap();
                symbols.insert(id, symbol.to_string());
            }
            let init = if l.reset <= 1 {
                Some(l.reset != 0)
            } else if l.reset == l.lit.into() {
                None
            } else {
                panic!()
            };
            latchs.push(AigLatch::new(id, AigEdge::from_lit(l.next), init));
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
            symbols,
        }
    }

    pub fn from_file<P: AsRef<Path>>(f: P) -> Self {
        let f = f.as_ref();
        let file = CString::new(f.to_str().unwrap()).unwrap();
        let mode = CString::new("r").unwrap();
        let file = unsafe { fopen(file.as_ptr(), mode.as_ptr()) };
        if file.is_null() {
            panic!("error: {} not found.", f.display());
        }
        let aiger = unsafe { aiger_init() };
        if !unsafe { aiger_read_from_file(aiger, file) }.is_null() {
            panic!("error: read {} failed.", f.display());
        }
        unsafe { fclose(file) };
        Self::from_aiger(aiger)
    }

    pub fn to_file<P: AsRef<Path>>(&self, f: P, ascii: bool) {
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
            let mut cs = CString::default();
            let s = if let Some(s) = self.get_symbol(self.nodes[*i].id) {
                cs = CString::new(s).unwrap();
                cs.as_ptr()
            } else {
                null()
            };
            unsafe {
                aiger_add_input(
                    aiger,
                    AigEdge::from(self.nodes[*i].id).to_lit().into(),
                    s as _,
                )
            };
            drop(cs);
        }
        for l in self.latchs.iter() {
            let mut cs = CString::default();
            let s = if let Some(s) = self.get_symbol(self.nodes[l.input].id) {
                cs = CString::new(s).unwrap();
                cs.as_ptr()
            } else {
                null()
            };
            let lit = AigEdge::from(self.nodes[l.input].id).to_lit();
            unsafe { aiger_add_latch(aiger, lit.into(), l.next.to_lit().into(), s as _) };
            drop(cs);
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
        let f = f.as_ref();
        let file = CString::new(f.to_str().unwrap()).unwrap();
        let mode = CString::new("w").unwrap();
        let file = unsafe { fopen(file.as_ptr(), mode.as_ptr()) };
        if file.is_null() {
            panic!("error: create {} failed.", f.display());
        }
        let mode = if ascii { 1 } else { 0 };
        let res = unsafe { aiger_write_to_file(aiger, mode, file) };
        assert!(res > 0, "write aig to {} failed", f.display());
        unsafe { fclose(file) };
    }
}
