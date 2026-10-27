use std::fmt;

use syn::token::In;

type Exp = u128;

#[derive(Clone, Copy)]
enum Symbol {
    R,
    S1,
    S3,
}

struct InfHeadCycleSim {
    x: Exp,
    y: Exp,
    n_cells: usize,
    rtape: Vec<Symbol>,
}

impl InfHeadCycleSim {
    fn new() -> Self {
        use Symbol::*;
        Self {
            x: 0,
            y: 0,
            n_cells: 0,
            rtape: vec![R, S1, S1, S3],
        }
    }

    fn step(&mut self) -> bool {
        use Symbol::*;
        match (self.x % 2, self.y % 2, self.rtape.last()) {
            (0, 0, Some(S3)) => {
                self.x = self.x / 2 + 1;
                self.y += self.x;
                self.rtape.pop();
                self.n_cells += 1;
                false
            }
            (0, 0, Some(S1)) => {
                self.y /= 2;
                self.x += self.y + 2;
                self.rtape.pop();
                self.n_cells += 1;
                false
            }
            (1, 1, Some(S3)) => {
                self.y /= 2;
                self.x += self.y + 3;
                self.rtape.pop();
                self.n_cells += 1;
                false
            }
            (1, 1, Some(S1)) => {
                self.x = self.x / 2 + 1;
                self.y += self.x + 1;
                self.rtape.pop();
                self.n_cells += 1;
                false
            }
            (_, _, Some(R)) if self.y == 0 => true,
            (_, _, Some(R)) => {
                self.x += 1;
                self.y -= 1;
                self.rtape.extend_from_slice(&[S1, S3]);
                false
            }
            _ => unimplemented!(),
        }
    }
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Symbol::*;
        match self {
            R => write!(f, "$"),
            S3 => write!(f, "3"),
            S1 => write!(f, "1"),
        }
    }
}

impl fmt::Display for InfHeadCycleSim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} cells: ({}, {})^inf ", self.n_cells, self.x, self.y)?;
        for s in self.rtape.iter().rev() {
            write!(f, "{s}")?;
        }
        Ok(())
    }
}

fn main() {
    let mut sim = InfHeadCycleSim::new();
    println!("{sim}");
    loop {
        let halted = sim.step();
        println!("{sim}");
        if halted {
            break;
        }
    }
}
