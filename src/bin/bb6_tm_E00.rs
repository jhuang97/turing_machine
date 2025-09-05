use turing_machine::{BasicSimulator, BasicStepInfo, State, Symbol, TMDirection, TuringMachine};

use std::fmt;
type Num = u64;

/// high level sim of the TM 1RB0LE_1RC0RF_1RD---_0LA1RB_1RB1LE_1LD1RF
struct ListSim {
    left: Vec<Num>,
    mid: Num,
    right: Vec<Num>,
    halted: bool,
    self_steps: u64,
}

impl fmt::Display for ListSim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, " {}: ", self.self_steps)?;

        for n in &self.left {
            write!(f, "{} ", n)?;
        }
        write!(f, "({})", self.mid)?;
        for n in self.right.iter().rev() {
            write!(f, " {}", n)?;
        }
        if self.halted {
            write!(f, " HALTED")?;
        }

        Ok(())
    }
}

fn add_or_merge(v: &mut Vec<Num>, nadd: Num) {
    if let Some(last) = v.last_mut() {
        *last += nadd;
    } else {
        v.push(nadd);
    }
}

impl ListSim {
    fn new() -> Self {
        Self {
            left: vec![],
            mid: 2,
            right: vec![],
            halted: false,
            self_steps: 0,
        }
    }

    fn step(&mut self) -> bool {
        match (self.mid, self.right.as_slice()) {
            // [...x, a, (2k), c, y...] --> [...x, a+k, (0), c+k, y...]  (k >= 1)
            (n @ 2.., _) if n % 2 == 0 => {
                let k = n/2;
                add_or_merge(&mut self.left, k);
                self.mid = 0;
                add_or_merge(&mut self.right, k);
            },

            // [...x, a, (2k+1), c, y...] --> [...x, (a+k), 1, c+k, y...] (k >= 1)
            (n @ 2.., _) if n % 2 == 1 => {
                let k = n/2;
                let a = self.left.pop().unwrap_or(0);
                self.mid = a + k;
                add_or_merge(&mut self.right, k);
                self.right.push(1);
            },

            // [...x, a, (1), y...] --> [...x, (a), 1, y...]
            (1, _) => {
                let a = self.left.pop().unwrap_or(0);
                self.mid = a;
                self.right.push(1);
            },

            // [...x, a, (0), b+3, ... z+1, 0^inf] --> [...x, a+4, b+1, ... (z), 1, 0^inf]
            (0, [rz, right_mid @ .., rb]) if *rb >= 3 => {
                assert!(*rz > 0);
                add_or_merge(&mut self.left, 4);
                self.left.push(*rb - 2);
                self.left.extend(right_mid.iter().rev());
                self.mid = *rz - 1;
                self.right = vec![1];
            },
            
            // [...x, a, (0), z+3, 0^inf] --> [...x, a+4, (z), 1, 0^inf]
            (0, [rz]) if *rz >= 3 => {
                add_or_merge(&mut self.left, 4);
                self.mid = *rz - 3;
                self.right = vec![1];
            }

            // [...x, a, (0), 2, b, y...] --> [...x, (a+3), b+1, y...]
            (0, [.., 2]) => {
                let a = self.left.pop().unwrap_or(0);
                self.mid = a + 3;
                self.right.pop();
                add_or_merge(&mut self.right, 1);
            }

            // [...x, (0), 1, ... z+1, 0^inf] --> Halt
            (0, [.., rz, 1]) => {
                assert!(*rz > 0);
                self.halted = true;
                return true;
            },

            // [...x, a, (0), 1, 0^inf] --> [...x, (a+5), 0^inf]
            (0, [1]) => {
                let a = self.left.pop().unwrap_or(0);
                self.mid = a + 5;
                self.right.clear();
            }

            _ => unimplemented!()
        }
        self.self_steps += 1;

        false
    }
}

fn main() {
    let mut sim = ListSim::new();
    println!("{sim}");
    for i in 0..1000000000000u64 {
        let halted = sim.step();
        // if sim.left.len() == 7 && sim.mid == 89 && sim.left.first() == Some(&75878333) {
        if (sim.left.len() <= 1 && (sim.left.first().is_some_and(|x| *x < 500) || (sim.left.len() == 0 && sim.mid < 500)))
            || i % 10000000000 == 0 {
            println!("{sim}");
        }
        if halted {
            break;
        }
    }
    println!("{sim}");
}

/// The numbers in parameters `left` and `right` are from left to right
fn config_to_raw_tape(left: Vec<usize>, mid: usize, right: Vec<usize>) -> (Vec<u8>, usize) {
    let mut tape = Vec::new();

    for term in left {
        for _ in 0..term {
            tape.push(1);
        }
        tape.push(0);
    }

    if tape.is_empty() && mid == 0 {
        tape.push(0);
    }

    let pos = tape.len() + mid - 1;
    for _ in 0..mid {
        tape.push(1);
    }
    tape.push(0);

    for term in right {
        tape.push(0);
        for _ in 0..term {
            tape.push(1);
        }
    }

    (tape, pos)
}

fn basic_sim() {
    let tm = TuringMachine::from_standard_notation("1RB0LE_1RC0RF_1RD---_0LA1RB_1RB1LE_1LD1RF");

    // let mut sim = BasicSimulator::new(tm.clone());
    let (tape, pos) = config_to_raw_tape(vec![], 0, vec![2]);
    let mut sim = BasicSimulator::from_tape(tm.clone(), &tape, 
        State::E, pos, Some(TMDirection::Left));

    println!("{}", sim.display_directed_head());
    let n_steps = 20;
    for _ in 0..n_steps {
        let BasicStepInfo { halted, record} = sim.step();
        // if filter(&sim) {
            println!("{}", sim.display_directed_head());
        // }
        if halted {
            return;
        }
    }
}