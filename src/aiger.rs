use crate::{Aig, AigEdge, AigNode};
use std::{
    fmt::{self, Display},
    fs::File,
    io::{self, BufRead, BufReader, BufWriter, Read, Write},
    path::Path,
};

// Helpers for AIG parsing
// In AIG format: literal = 2 * variable_index + sign_bit
// where sign_bit = 0 for positive, 1 for negated
#[inline]
fn lit_to_var(lit: u32) -> u32 {
    lit >> 1
}
#[inline]
fn lit_is_negated(lit: u32) -> bool {
    (lit & 1) != 0
}
#[inline]
fn lit_to_aigedge(lit: u32) -> AigEdge {
    let var = lit_to_var(lit);
    let negated = lit_is_negated(lit);
    AigEdge::new(var as usize, negated)
}
// Delta decoder for binary AIG format
// Variable-length encoding: 7 bits per byte, MSB indicates continuation
struct DeltaDecoder<R: Read> {
    reader: R,
}
impl<R: Read> DeltaDecoder<R> {
    fn new(reader: R) -> Self {
        Self { reader }
    }
    fn read_delta(&mut self) -> io::Result<u32> {
        let mut result = 0u32;
        let mut shift = 0;
        loop {
            let mut buf = [0u8; 1];
            self.reader.read_exact(&mut buf)?;
            let byte = buf[0];
            // Extract lower 7 bits
            let value = (byte & 0x7f) as u32;
            result |= value << shift;
            // If MSB is 0, this is the last byte
            if (byte & 0x80) == 0 {
                break;
            }
            shift += 7;
        }
        Ok(result)
    }
}

impl Aig {
    pub fn from_file_r<P: AsRef<Path>>(path: P) -> io::Result<Aig> {
        let file = File::open(path.as_ref())?;
        let mut reader = BufReader::new(file);
        // Read header line
        let mut header_line = String::new();
        reader.read_line(&mut header_line)?;
        let is_ascii = header_line.starts_with("aag ");
        let parts: Vec<&str> = header_line.split_whitespace().collect();
        // maxvar is not necessary
        // let maxvar: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_inputs: u32 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_latches: u32 = parts.get(3).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_outputs: u32 = parts.get(4).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_ands: u32 = parts.get(5).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_bad: u32 = parts.get(6).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_constraints: u32 = parts.get(7).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_justice: u32 = parts.get(8).and_then(|s| s.parse().ok()).unwrap_or(0);
        let num_fairness: u32 = parts.get(9).and_then(|s| s.parse().ok()).unwrap_or(0);

        // Initialize Aig structure
        let mut aig = Aig::new();
        let node_len = (num_inputs + num_latches + num_ands + 1) as usize;
        aig.nodes.reserve(node_len - 1); // -1 because we already have node 0
        // helper
        let e = |msg: &str| io::Error::new(io::ErrorKind::InvalidData, msg);

        for i in 0..num_inputs {
            if is_ascii {
                // In ASCII format, input literals are explicitly listed
                let mut line = String::new();
                reader.read_line(&mut line)?;
                let lit: u32 = line.parse().map_err(|_| e("Invalid input literal"))?;
                let var = lit_to_var(lit) as usize;
                // Ensure we have nodes up to this variable
                while aig.nodes.len() <= var {
                    aig.nodes.push(AigNode {
                        id: aig.nodes.len(),
                        typ: crate::AigNodeType::Leaf,
                    });
                }
                aig.add_input(var);
            } else {
                // In binary format, inputs are implicit: literals 2, 4, 6, ...
                let var = (i + 1) as usize;
                let input = aig.new_input();
                assert_eq!(input, var);
            }
        }

        // Read latches - format: latch_lit next_lit [reset_lit]
        for i in 0..num_latches {
            let mut line = String::new();
            reader.read_line(&mut line)?;
            let parts: Vec<&str> = line.split_whitespace().collect();
            if is_ascii {
                // In ASCII format, latch literals are explicitly listed
                let latch_lit: u32 = parts.get(0).and_then(|s| s.parse().ok()).unwrap_or(0);
                let latch_var = lit_to_var(latch_lit) as usize;
                // Ensure we have nodes up to this variable
                while aig.nodes.len() <= latch_var {
                    aig.nodes.push(AigNode {
                        id: aig.nodes.len(),
                        typ: crate::AigNodeType::Leaf,
                    });
                }
                let next_lit: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
                let next = lit_to_aigedge(next_lit);
                // Optional reset literal - default is 0 (constant false)
                let reset_lit: u32 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
                let reset_var = lit_to_var(reset_lit);
                // If reset literal equals latch literal, init is None (uninitialized)
                let init = if reset_var == latch_var as u32 {
                    None
                } else {
                    Some(lit_to_aigedge(reset_lit))
                };
                aig.add_latch(latch_var, next, init);
            } else {
                // In binary format, latch literals are implicit:
                // 2*(num_inputs+1), 2*(num_inputs+2), ...
                let latch_var = (num_inputs + i + 1) as usize;
                let latch_input = aig.new_leaf_node();
                assert_eq!(latch_input, latch_var);
                let next_lit: u32 = parts.get(0).and_then(|s| s.parse().ok()).unwrap_or(0);
                let next = lit_to_aigedge(next_lit);
                // Optional reset literal - default is 0 (constant false) if not provided
                let reset_lit: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
                let reset_var = lit_to_var(reset_lit);
                // If reset literal equals latch literal, init is None (uninitialized)
                let init = if reset_var == latch_var as u32 {
                    None
                } else {
                    Some(lit_to_aigedge(reset_lit))
                };
                aig.add_latch(latch_input, next, init);
            }
        }

        // Read aigEdge helper
        let ae = |v: &mut Vec<AigEdge>, reader: &mut BufReader<File>, sz: usize| {
            for _ in 0..sz {
                let mut line = String::new();
                reader.read_line(&mut line)?;
                let lit: u32 = line.trim().parse().map_err(|_| e("Bad literal"))?;
                v.push(lit_to_aigedge(lit));
            }
            Ok::<(), std::io::Error>(())
        };
        ae(&mut aig.outputs, &mut reader, num_outputs as usize)?;
        ae(&mut aig.bads, &mut reader, num_bad as usize)?;
        ae(&mut aig.constraints, &mut reader, num_constraints as usize)?;
        // Read justice properties (size followed by literals)
        let mut justice_sizes = Vec::new();
        for _ in 0..num_justice {
            let mut line = String::new();
            reader.read_line(&mut line)?;
            let size: u32 = line.trim().parse().map_err(|_| e("Invalid justice size"))?;
            justice_sizes.push(size);
        }
        for size in justice_sizes {
            let mut justice_lits = Vec::new();
            ae(&mut justice_lits, &mut reader, size as usize)?;
            aig.justice.push(justice_lits);
        }
        ae(&mut aig.fairness, &mut reader, num_fairness as usize)?;

        if is_ascii {
            // Read AND gates in ASCII format: lhs rhs0 rhs1
            for _ in 0..num_ands {
                let mut line = String::new();
                reader.read_line(&mut line)?;
                let parts: Vec<&str> = line.split_whitespace().collect();
                let lhs: u32 = parts.get(0).and_then(|s| s.parse().ok()).unwrap_or(0);
                let rhs0: u32 = parts.get(1).and_then(|s| s.parse().ok()).unwrap_or(0);
                let rhs1: u32 = parts.get(2).and_then(|s| s.parse().ok()).unwrap_or(0);
                let var = lit_to_var(lhs) as usize;
                // Ensure we have nodes up to this variable
                while aig.nodes.len() <= var {
                    aig.nodes.push(AigNode {
                        id: aig.nodes.len(),
                        typ: crate::AigNodeType::Leaf,
                    });
                }
                // Replace the leaf node with an AND node
                aig.nodes[var] = AigNode::new_and(var, lit_to_aigedge(rhs0), lit_to_aigedge(rhs1));
            }
        } else {
            // Read AND gates in binary format using delta encoding
            // The delta decoder will consume exactly the bytes needed for AND gates,
            // leaving the reader positioned at the symbol table
            let mut delta_decoder = DeltaDecoder::new(reader);
            let mut lhs = 2 * (num_inputs + num_latches + 1);
            for _ in 0..num_ands {
                let delta0 = delta_decoder.read_delta()?;
                let rhs0 = lhs - delta0;
                let delta1 = delta_decoder.read_delta()?;
                let rhs1 = rhs0 - delta1;
                // Add AND gate to aig
                let var = lit_to_var(lhs) as usize;
                aig.nodes.push(AigNode::new_and(
                    var,
                    lit_to_aigedge(rhs0),
                    lit_to_aigedge(rhs1),
                ));
                lhs += 2;
            }
            reader = delta_decoder.reader;
        }

        // Parse symbol table
        let mut line = String::new();
        while reader.read_line(&mut line)? > 0 {
            if line == "c" {
                break;
            }
            // Parse symbol: type + index + space + name
            let space_pos = line.find(' ').unwrap_or(0);
            if space_pos == 0 {
                line.clear();
                continue;
            }
            let prefix = &line[..space_pos];
            let name = &line[space_pos + 1..];
            let symbol_type = prefix.chars().next().unwrap_or('a');
            let index_str = &prefix[1..];
            if let Ok(index) = index_str.parse::<usize>() {
                let var = match symbol_type {
                    'i' => aig.inputs.get(index).and_then(|s| Some(s.clone())),
                    'l' => aig.latchs.get(index).and_then(|s| Some(s.input)),
                    _ => None,
                };
                if let Some(v) = var {
                    aig.set_symbol(v, name);
                }
            }
            line.clear();
        }
        Ok(aig)
    }

    pub fn from_file<P: AsRef<Path>>(f: P) -> Self {
        Self::from_file_r(f.as_ref()).unwrap_or_else(|e| {
            panic!("error: failed to read {}: {}", f.as_ref().display(), e);
        })
    }
    pub fn to_file<P: AsRef<Path>>(&self, f: P, ascii: bool) {
        if !ascii {
            unimplemented!("binary AIG output");
        }
        let mut w = BufWriter::new(File::create(&f).unwrap());
        write!(&mut w, "{}", self).unwrap();
    }
}

impl Display for Aig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> std::fmt::Result {
        // Helper to convert AigEdge to literal
        let edge_to_lit = |edge: &AigEdge| -> u32 {
            (edge.node_id() as u32) * 2 + if edge.compl() { 1 } else { 0 }
        };
        let maxvar = self.nodes.len() - 1;
        let num_ands = self.nodes.iter().filter(|n| n.is_and()).count();
        write!(
            f,
            "aag {} {} {} {} {}",
            maxvar,
            self.inputs.len(),
            self.latchs.len(),
            self.outputs.len(),
            num_ands
        )?;

        let emp = !self.bads.is_empty() as usize * 8
            + !self.constraints.is_empty() as usize * 4
            + !self.justice.is_empty() as usize * 2
            + !self.fairness.is_empty() as usize;
        // Optional header fields
        if emp != 0 {
            write!(f, " {}", self.bads.len())?;
            if emp & 7 != 0 {
                write!(f, " {}", self.constraints.len())?;
                if emp & 3 != 0 {
                    write!(f, " {}", self.justice.len())?;
                    if emp & 1 != 0 {
                        write!(f, " {}", self.fairness.len())?;
                    }
                }
            }
        }
        writeln!(f)?;

        for &input_id in &self.inputs {
            writeln!(f, "{}", input_id * 2)?;
        }
        for latch in &self.latchs {
            let w = if let Some(init) = &latch.init {
                edge_to_lit(init) as usize
            } else {
                latch.input * 2
            };
            writeln!(f, "{} {} {}", latch.input * 2, edge_to_lit(&latch.next), w)?;
        }
        for output in &self.outputs {
            writeln!(f, "{}", edge_to_lit(output))?;
        }
        for bad in &self.bads {
            writeln!(f, "{}", edge_to_lit(bad))?;
        }
        for constraint in &self.constraints {
            writeln!(f, "{}", edge_to_lit(constraint))?;
        }
        // sizes first, then all literals
        for justice_prop in &self.justice {
            writeln!(f, "{}", justice_prop.len())?;
        }
        for justice_prop in &self.justice {
            for lit in justice_prop {
                writeln!(f, "{}", edge_to_lit(lit))?;
            }
        }
        for fairness in &self.fairness {
            writeln!(f, "{}", edge_to_lit(fairness))?;
        }
        for node in &self.nodes {
            if node.is_and() {
                let (fanin0, fanin1) = node.fanin();
                writeln!(
                    f,
                    "{} {} {}",
                    node.node_id() * 2,
                    edge_to_lit(&fanin1),
                    edge_to_lit(&fanin0)
                )?;
            }
        }

        // Write symbol table
        for (i, &input_id) in self.inputs.iter().enumerate() {
            if let Some(name) = self.get_symbol(input_id) {
                writeln!(f, "i{} {}", i, name)?;
            }
        }
        for (i, latch) in self.latchs.iter().enumerate() {
            if let Some(name) = self.get_symbol(latch.input) {
                writeln!(f, "l{} {}", i, name)?;
            }
        }
        for (i, output) in self.outputs.iter().enumerate() {
            if let Some(name) = self.get_symbol(output.node_id()) {
                writeln!(f, "o{} {}", i, name)?;
            }
        }
        for (i, bad) in self.bads.iter().enumerate() {
            if let Some(name) = self.get_symbol(bad.node_id()) {
                writeln!(f, "b{} {}", i, name)?;
            }
        }
        for (i, constraint) in self.constraints.iter().enumerate() {
            if let Some(name) = self.get_symbol(constraint.node_id()) {
                writeln!(f, "c{} {}", i, name)?;
            }
        }
        for (i, justice_prop) in self.justice.iter().enumerate() {
            // Justice properties can have symbols on the property itself
            // Check the first literal's node for a symbol
            if !justice_prop.is_empty() {
                if let Some(name) = self.get_symbol(justice_prop[0].node_id()) {
                    writeln!(f, "j{} {}", i, name)?;
                }
            }
        }
        for (i, fairness) in self.fairness.iter().enumerate() {
            if let Some(name) = self.get_symbol(fairness.node_id()) {
                writeln!(f, "f{} {}", i, name)?;
            }
        }
        Ok(())
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
