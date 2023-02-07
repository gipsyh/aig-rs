use crate::AigEdge;
use std::ops::{Add, Deref, DerefMut, Not};

#[derive(Clone, Debug)]
pub struct AigClause {
    lits: Vec<AigEdge>,
}

impl AigClause {
    pub fn new() -> Self {
        AigClause { lits: Vec::new() }
    }
}

impl Default for AigClause {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for AigClause {
    type Target = Vec<AigEdge>;

    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for AigClause {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl Not for AigClause {
    type Output = AigCube;

    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        AigCube { lits }
    }
}

impl<F: Into<Vec<AigEdge>>> From<F> for AigClause {
    fn from(value: F) -> Self {
        Self { lits: value.into() }
    }
}

impl FromIterator<AigEdge> for AigClause {
    fn from_iter<T: IntoIterator<Item = AigEdge>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
        }
    }
}

#[derive(Clone, Debug)]
pub struct AigCube {
    lits: Vec<AigEdge>,
}

impl AigCube {
    pub fn new() -> Self {
        AigCube { lits: Vec::new() }
    }
}

impl Default for AigCube {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for AigCube {
    type Target = Vec<AigEdge>;

    fn deref(&self) -> &Self::Target {
        &self.lits
    }
}

impl DerefMut for AigCube {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.lits
    }
}

impl Not for AigCube {
    type Output = AigClause;

    fn not(self) -> Self::Output {
        let lits = self.lits.iter().map(|lit| !*lit).collect();
        AigClause { lits }
    }
}

impl<F: Into<Vec<AigEdge>>> From<F> for AigCube {
    fn from(value: F) -> Self {
        Self { lits: value.into() }
    }
}

impl FromIterator<AigEdge> for AigCube {
    fn from_iter<T: IntoIterator<Item = AigEdge>>(iter: T) -> Self {
        Self {
            lits: Vec::from_iter(iter),
        }
    }
}

#[derive(Clone, Debug)]
pub struct AigCnf {
    clauses: Vec<AigClause>,
}

impl AigCnf {
    pub fn new() -> Self {
        Self {
            clauses: Vec::new(),
        }
    }

    pub fn add_clause(&mut self, clause: AigClause) {
        self.clauses.push(clause);
    }
}

impl Default for AigCnf {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for AigCnf {
    type Target = Vec<AigClause>;

    fn deref(&self) -> &Self::Target {
        &self.clauses
    }
}

impl DerefMut for AigCnf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.clauses
    }
}

#[derive(Clone, Debug)]
pub struct AigDnf {
    cubes: Vec<AigCube>,
}

impl AigDnf {
    pub fn new() -> Self {
        Self { cubes: Vec::new() }
    }

    pub fn add_cube(&mut self, cube: AigCube) {
        self.cubes.push(cube);
    }
}

impl Default for AigDnf {
    fn default() -> Self {
        Self::new()
    }
}

impl Deref for AigDnf {
    type Target = Vec<AigCube>;

    fn deref(&self) -> &Self::Target {
        &self.cubes
    }
}

impl DerefMut for AigDnf {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.cubes
    }
}

impl Add for AigDnf {
    type Output = Self;

    fn add(mut self, mut rhs: Self) -> Self::Output {
        self.cubes.append(&mut rhs.cubes);
        self
    }
}

impl Not for AigDnf {
    type Output = AigCnf;

    fn not(self) -> Self::Output {
        let mut cnf = AigCnf::new();
        for cube in self.cubes {
            cnf.add_clause(!cube);
        }
        cnf
    }
}
