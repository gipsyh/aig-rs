use crate::{Aig, AigCube, AigEdge};

impl Aig {
    pub fn latch_init_cube(&self) -> AigCube {
        AigCube::from_iter(
            self.latchs
                .iter()
                .filter_map(|l| l.init.map(|init| AigEdge::new(l.input, !init))),
        )
    }
}
