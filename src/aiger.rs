use crate::{Aig, AigEdge, AigLatch, AigNode};
use giputils::hash::GHashMap;
use libc::{FILE, c_int, fclose, fopen};
use logicrs::Lit;
use std::{
    ffi::{CStr, CString, c_char, c_void},
    fmt::{self, Display, Write},
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
    fn aiger_add_justice(aiger: *mut c_void, size: u32, lits: *mut u32, s: *const c_char);
    fn aiger_add_fairness(aiger: *mut c_void, lit: u32, s: *const c_char);
    fn aiger_add_and(aiger: *mut c_void, lhs: u32, rhs0: u32, rhs1: u32);
    fn aiger_add_reset(aiger: *mut c_void, lit: u32, reset: u32);
    fn aiger_write_to_file(aiger: *mut c_void, mode: i32, file: *mut FILE) -> i32;
    fn aiger_write_generic(
        aiger: *mut c_void,
        mode: i32,
        state: *mut c_void,
        aiger_put: unsafe extern "C" fn(c_char, *mut c_void) -> c_int,
    ) -> i32;

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
    reset: Lit,
    size: u32,
    lits: *mut Lit,
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
            let init = if l.reset.var() == l.lit.var() {
                assert!(l.reset == l.lit);
                None
            } else {
                Some(AigEdge::from_lit(l.reset))
            };
            latchs.push(AigLatch {
                input: id,
                next: AigEdge::from_lit(l.next),
                init,
            });
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
        let justice: Vec<Vec<AigEdge>> = (0..aiger.num_justice)
            .map(|i| unsafe { *aiger.justice.add(i as usize) })
            .map(|l| {
                (0..l.size)
                    .map(|j| unsafe { AigEdge::from_lit(*l.lits.add(j as usize)) })
                    .collect()
            })
            .collect();
        let fairness: Vec<AigEdge> = (0..aiger.num_fairness)
            .map(|i| unsafe { *aiger.fairness.add(i as usize) })
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
            justice,
            fairness,
        }
    }

    fn to_aiger(&self) -> *mut Aiger {
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
            let reset: Lit = if let Some(i) = l.init {
                i.to_lit()
            } else {
                lit
            };
            unsafe { aiger_add_reset(aiger, lit.into(), reset.into()) };
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
        for j in self.justice.iter() {
            let j: Vec<_> = j.iter().map(|e| e.to_lit()).collect();
            unsafe {
                aiger_add_justice(
                    aiger,
                    j.len() as _,
                    j.as_slice().as_ptr() as *mut u32,
                    null() as _,
                );
            }
        }
        for l in self.fairness.iter() {
            unsafe { aiger_add_fairness(aiger, l.to_lit().into(), null() as _) };
        }
        aiger as _
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
        let aiger = self.to_aiger();
        let f = f.as_ref();
        let file = CString::new(f.to_str().unwrap()).unwrap();
        let mode = CString::new("w").unwrap();
        let file = unsafe { fopen(file.as_ptr(), mode.as_ptr()) };
        if file.is_null() {
            panic!("error: create {} failed.", f.display());
        }
        let mode = if ascii { 1 } else { 0 };
        let res = unsafe { aiger_write_to_file(aiger as _, mode, file) };
        assert!(res > 0, "write aig to {} failed", f.display());
        unsafe { fclose(file) };
        unsafe {
            aiger_reset(aiger as _);
        }
    }
}

unsafe extern "C" fn aiger_put(ch: c_char, state: *mut c_void) -> c_int {
    let pc = unsafe { &mut *(state as *mut fmt::Formatter) };
    pc.write_char(ch as u8 as char).unwrap();
    ch as c_int
}

impl Display for Aig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        let aiger = self.to_aiger();
        let res = unsafe { aiger_write_generic(aiger as _, 1, f as *mut _ as _, aiger_put) };
        unsafe {
            aiger_reset(aiger as _);
        }
        if res > 0 { Ok(()) } else { Err(fmt::Error) }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test() {
        let mut aig = Aig::new();
        let i0: AigEdge = aig.new_input().into();
        let i1: AigEdge = aig.new_input().into();
        aig.new_and_node(i0, i1);
        println!("{aig}");
    }
}
