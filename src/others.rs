use crate::{Aig, AigCube, AigEdge};

impl Aig {
    pub fn latch_init_cube(&self) -> AigCube {
        AigCube::from_iter(self.latchs.iter().map(|l| Into::<AigEdge>::into(l.input)))
    }
}
