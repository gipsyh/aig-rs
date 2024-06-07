use crate::{Aig, AigEdge};
use std::{collections::HashMap, mem::swap};

impl Aig {
    pub fn strash(&self) -> Self {
        let mut map = HashMap::new();
        let mut strash_map = HashMap::new();
        for node in self.nodes.iter() {
            if node.is_and() {
                let mut fanin0 = node.fanin0();
                if let Some(eq) = strash_map.get(&fanin0.node_id()) {
                    fanin0 = AigEdge::new(*eq, fanin0.complement);
                }
                let mut fanin1 = node.fanin1();
                if let Some(eq) = strash_map.get(&fanin1.node_id()) {
                    fanin1 = AigEdge::new(*eq, fanin1.complement);
                }
                if fanin0.node_id() > fanin1.node_id() {
                    swap(&mut fanin0, &mut fanin1);
                }
                match map.get(&(fanin0, fanin1)) {
                    Some(eq) => {
                        strash_map.insert(node.node_id(), *eq);
                    }
                    None => {
                        map.insert((fanin0, fanin1), node.id);
                    }
                }
            }
        }
        println!("{:?}", strash_map.len());
        println!("{:?}", map.len());
        todo!()
    }
}
