use crate::AigEdge;
use std::ops::{Add, Deref, DerefMut, Not};

#[derive(Clone, Debug)]
pub struct Clause {
    lits: Vec<AigEdge>,
}

impl Clause {
    pub fn new() -> Self {
        Clause { lits: Vec::new() }
    }
}

impl Default for Clause {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Clause {
    type Target = Vec<AigEdge>;

    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for Clause {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl<const N: usize> From<[AigEdge; N]> for Clause {
    fn from(s: [AigEdge; N]) -> Self {
        Self {
            lits: <[AigEdge]>::into_vec(Box::new(s)),
        }
    }
}

#[derive(Clone, Debug)]
pub struct Cube {
    lits: Vec<AigEdge>,
}

impl Cube {
    pub fn new() -> Self {
        Cube { lits: Vec::new() }
    }
}

impl Default for Cube {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Cube {
    type Target = Vec<AigEdge>;

    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for Cube {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl Not for Cube {
    type Output = Clause;

    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        Clause { lits }
    }
}

#[derive(Clone, Debug)]
pub struct Cnf {
    clauses: Vec<Clause>,
}

impl Cnf {
    pub fn new() -> Self {
        Self {
            clauses: Vec::new(),
        }
    }

    pub fn add_clause(&mut self, clause: Clause) {
        self.clauses.push(clause);
    }
}

impl Default for Cnf {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Cnf {
    type Target = Vec<Clause>;

    fn deref(&self) -> &Self::Target {
        &self.clauses
    }
}

impl DerefMut for Cnf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.clauses
    }
}

#[derive(Clone, Debug)]
pub struct Dnf {
    cubes: Vec<Cube>,
}

impl Dnf {
    pub fn new() -> Self {
        Self { cubes: Vec::new() }
    }

    pub fn add_cube(&mut self, cube: Cube) {
        self.cubes.push(cube);
    }
}

impl Default for Dnf {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for Dnf {
    type Target = Vec<Cube>;

    fn deref(&self) -> &Self::Target {
        &self.cubes
    }
}

impl DerefMut for Dnf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cubes
    }
}

impl Add for Dnf {
    type Output = Self;

    fn add(mut self, mut rhs: Self) -> Self::Output {
        self.cubes.append(&mut rhs.cubes);
        self
    }
}

impl Not for Dnf {
    type Output = Cnf;

    fn not(self) -> Self::Output {
        let mut cnf = Cnf::new();
        for cube in self.cubes {
            cnf.add_clause(!cube);
        }
        cnf
    }
}
