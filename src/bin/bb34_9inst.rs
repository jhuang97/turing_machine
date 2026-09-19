use std::fmt;

#[derive(Clone, Copy, PartialEq, Eq)]
enum Symbol {
    R,
    S2,
    S3,
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Symbol::*;
        match self {
            R => write!(f, "$"),
            S2 => write!(f, "2"),
            S3 => write!(f, "3"),
        }
    }
}

struct Sim {
    x: u64,
    y: u64,
    right: Vec<Symbol>,
    steps: u64,
    cells: u64,
}

impl Sim {
    fn new() -> Self {
        use Symbol::*;
        Self {
            x: 0,
            y: 0,
            right: vec![R, S2, S2, S2],
            steps: 0,
            cells: 0,
        }
    }

    /// L C> 2 3^4 2 3 2^26 R
    fn new2() -> Self {
        use Symbol::*;
        let mut right = vec![R];
        for _ in 0..26 {
            right.push(S2);
        }
        right.extend_from_slice(&[S3, S2, S3, S3, S3, S3, S2]);
        Self {
            x: 0,
            y: 0,
            right,
            steps: 0,
            cells: 0,
        }
    }

    fn step(&mut self) {
        use Symbol::*;
        if self.y % 2 == 1 {
            match self.right.last_mut() {
                Some(r @ S2) => *r = S3,
                Some(S3) => {
                    println!("odd facing 3...");
                    let mut i = self.right.len() - 1;
                    loop {
                        assert!(i > 0);

                        if self.right[i] == S3 {
                            // b 3 -> 2 b
                            self.right[i] = S2;
                            i -= 1;
                        } else if self.right[i] == S2 {
                            // b 2 -> 3
                            self.right[i] = S3;
                            break;
                        } else {
                            unimplemented!();
                        }
                    }
                }
                Some(R) => self.right.extend_from_slice(&[S2, S2]),
                None => unreachable!(),
            }
            self.x += 1;
            self.y -= 1;
        } else {
            match self.right.last() {
                Some(R) => {
                    if self.y > 0 {
                        self.right.extend_from_slice(&[S2, S2]);
                        self.x += 1;
                        self.y -= 1;
                    } else {
                        unimplemented!()
                    }
                }
                Some(S2) => {
                    assert!(self.x % 2 == 0);
                    self.x = self.x / 2 + 1;
                    self.y += self.x;
                    self.right.pop();
                    self.cells += 1;
                }
                Some(S3) => {
                    assert!(self.x % 2 == 0);
                    self.y /= 2;
                    self.x += self.y + 2;
                    self.right.pop();
                    self.cells += 1;
                }
                None => unreachable!(),
            }
        }
        self.steps += 1;
    }
}

impl fmt::Display for Sim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{},{} | {},{} ", self.steps, self.cells, self.x, self.y)?;
        for s in self.right.iter().rev() {
            write!(f, "{}", s)?;
        }
        Ok(())
    }
}

fn main() {
    let mut sim = Sim::new();
    // let mut sim = Sim::new2();
    println!("{sim}");
    for k in 0..1000000 {
        sim.step();
        if k < 100 || k % 100 == 0 || k > 14000 {
            println!("{sim}");
        }
    }
}
