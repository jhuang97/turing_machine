use std::{collections::VecDeque, fmt, usize};

use turing_machine::{DirectedHeadConfig, DirectedHeadSimulator, DirectedHeadStepResult, GeneralSymbol, State, Symbol, TMDirection, TuringMachine};

fn measure_left_side_heads() {
    let tm = TuringMachine::from_standard_notation("1RB3RB1LA2LA3RA_1LB2RA4RB0LA---");

    let config = DirectedHeadConfig::parse_str("^1444442323 B>", true).unwrap();
    let mut sim = DirectedHeadSimulator::new_with_time(&config, &tm, usize::MAX);
    let mut heads: Vec<State> = Vec::new();

    println!("\n{}: {}", sim.time, sim.config);
    while sim.config.left_tape.len() < 28 {
        if sim.config.right_tape.len() == 1 && sim.config.dir == TMDirection::Right {
            print!("{:<6}: {:>32} | ", sim.time, format!("{}", sim.config));
            heads.push(sim.config.state);
            sim.config.state = State::A;
            sim.config.dir = TMDirection::Left;
            for h in heads.iter().rev() {
                match h {
                    State::A => print!("a"),
                    State::B => print!("b"),
                    _ => (),
                }
            }
            println!();
        }
        let res = sim.step();
        if res != DirectedHeadStepResult::Success {
            println!("{:?}", res);
        }
        // println!("{}: {}", sim.time, sim.config);
    }
}

const fn parse_heads<const LEN: usize>(bytes: &[u8]) -> [LongSymbol; LEN] {
    let mut res = [LongSymbol::Ha; LEN];

    let mut i = 0;
    while i < LEN {
        match bytes[i] {
            b'a' => res[i] = LongSymbol::Ha,
            b'b' => res[i] = LongSymbol::Hb,
            _ => panic!("invalid head character"),
        }
        i += 1;
    }
    res
}


#[derive(Clone, Copy, PartialEq, Eq)]
enum LongSymbol {
    Ha, Hb, Hab,
    S1, S2, RB, R29
}

impl fmt::Display for LongSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        match self {
            Self::Ha => write!(f, "{}", "a".red().bold()),
            Self::Hb => write!(f, "{}", "b".red().bold()),
            Self::Hab => write!(f, "{}", "ab".red().bold().underline()),
            Self::S1 => write!(f, "1"),
            Self::S2 => write!(f, "2"),
            Self::RB => write!(f, "{}", "RB".bold()),
            Self::R29 => write!(f, "{}", "R29".bold()),
        }
    }
}

struct LongSim {
    head_generator: Box<dyn Iterator<Item = LongSymbol>>,

    /// head_generator feeds into front of near_tape, back of near_tape connects with end_tape
    near_tape: VecDeque<LongSymbol>,

    /// must not contain heads
    end_tape: Vec<LongSymbol>,
    head_steps: u64,
    self_move_steps: u64,
}

impl LongSim {
    fn new() -> Self {
        const HEAD_SEQ_STR: &[u8] = b"baabbabbabaaabba";
        const HEAD_SEQ: [LongSymbol; HEAD_SEQ_STR.len()] = parse_heads(HEAD_SEQ_STR);
        let head_generator = Box::new(HEAD_SEQ.iter().cloned().cycle());

        let mut end_tape = vec![LongSymbol::RB];
        const INIT_SYMBOLS: &[u8] = b"21122211112212211122111222111211111222122221211211211112212112222212212112";
        for b in INIT_SYMBOLS.iter().rev() {
            match b {
                b'1' => end_tape.push(LongSymbol::S1),
                b'2' => end_tape.push(LongSymbol::S2),
                _ => panic!("invalid tape symbol"),
            }
        }

        Self {
            head_generator, near_tape: VecDeque::new(), end_tape,
            head_steps: 0, self_move_steps: 0,
        }
    }

    fn step(&mut self) -> bool {
        use LongSymbol::*;
        let is_head_step = match (self.near_tape.back(), self.end_tape.last()) {
            (None, _) => {
                self.near_tape.push_front(self.head_generator.next().unwrap());
                true
            },
            // a 1 -> 2 b
            (Some(Ha), Some(S1)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S2);
                self.near_tape.push_back(Hb);
                true
            },
            // b 1 -> 1 a
            (Some(Hb), Some(S1)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S1);
                self.near_tape.push_back(Ha);
                true
            },
            // ab 1 -> 2 ba
            (Some(Hab), Some(S1)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S2);
                self.near_tape.push_back(Hb);
                self.near_tape.push_back(Ha);
                true
            }
            // a 2 -> 1
            (Some(Ha), Some(S2)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.end_tape.push(S1);
                true
            },
            // b 2 -> 2 a b
            (Some(Hb), Some(S2)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S2);
                self.near_tape.push_back(Hab);
                // self.near_tape.push_back(Ha);
                // self.near_tape.push_back(Hb);
                true
            },
            // ab 2 -> 1 ab
            (Some(Hab), Some(S2)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S1);
                self.near_tape.push_back(Hab);
                true
            },
            // ab ?
            (Some(Hab), Some(_)) => {
                self.near_tape.pop_back();
                self.near_tape.push_back(Ha);
                self.near_tape.push_back(Hb);
                true
            },
            // a RB -> 211 R29
            (Some(Ha), Some(RB)) => {
                self.debug_print();
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.end_tape.extend_from_slice(&[R29, S1, S1, S2]);
                true
            },
            // b RB -> 1221222 RB
            (Some(Hb), Some(RB)) => {
                self.near_tape.pop_back();
                self.end_tape.extend_from_slice(&[S2, S2, S2, S1, S2, S2, S1]);
                true
            },
            // a R29 -> ?
            (Some(Ha), Some(R29)) => {
                self.debug_print();
                unimplemented!();
            },
            // b R29 -> 2222 RB
            (Some(Hb), Some(R29)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.end_tape.extend_from_slice(&[RB, S2, S2, S2, S2]);
                true
            },
            (Some(_), _) => {
                self.end_tape.push(self.near_tape.pop_back().unwrap());
                false
            },
        };
        if is_head_step {
            self.head_steps += 1;
        } else {
            self.self_move_steps += 1;
        }
        is_head_step
    }

    fn debug_print(&self) {
        let cell_count = self.near_tape.iter().filter(|&&s| s != LongSymbol::Ha && s != LongSymbol::Hb).count();
        eprintln!("{self}, {cell_count} cells");
    }
}

impl fmt::Display for LongSim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        self.head_steps.fmt(f)?;
        write!(f, ": (...) ")?;

        const LEFT_PRINT_THRESHOLD: usize = 90;
        let l_th = LEFT_PRINT_THRESHOLD / 2;
        if self.near_tape.len() <= LEFT_PRINT_THRESHOLD {
            for symb in &self.near_tape {
                write!(f, "{}", symb)?;
            }
        } else {
            let mut iter = self.near_tape.iter();
            for _ in 0..l_th {
                write!(f, "{}", iter.next().unwrap())?;
            }
            write!(f, " ...{} terms... ", self.near_tape.len() - LEFT_PRINT_THRESHOLD)?;
            for i in self.near_tape.len() - l_th..self.near_tape.len() {
                write!(f, "{}", self.near_tape.get(i).unwrap())?;
            }
        }
        write!(f, " ")?;
        const RIGHT_PRINT_THRESHOLD: usize = 50;
        let r_th = RIGHT_PRINT_THRESHOLD / 2;
        if self.end_tape.len() <= RIGHT_PRINT_THRESHOLD {
            for symb in self.end_tape.iter().rev() {
                write!(f, "{}", symb)?;
            }
        } else {
            for symb in self.end_tape[self.end_tape.len() - r_th..].iter().rev() {
                write!(f, "{}", symb)?;
            }
            write!(
                f, " ...{} terms... ", self.end_tape.len() - RIGHT_PRINT_THRESHOLD
            )?;
            for symb in self.end_tape[..r_th].iter().rev() {
                write!(f, "{}", symb)?;
            }
        }
        Ok(())
    }
}

fn main() {
    // measure_left_side_heads();

    let mut sim = LongSim::new();
    println!("{sim}");

    let max_steps = 1000000000000u64;
    //                    516000000000
    // let max_steps = 1800;
    for i in 0..=max_steps {
        if sim.step() && sim.head_steps % 1000000000 == 0
        {
            println!("{sim}");
        }
    }
}