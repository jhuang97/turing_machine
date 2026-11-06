use std::{collections::VecDeque, fmt};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum LongHead {
    A,
    B,
    C,
    D,
}

impl fmt::Display for LongHead {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self {
            LongHead::D => write!(f, "d"),
            _ => write!(f, "{:?}", self),
        }
    }
}

struct InfHeadCycle(VecDeque<LongHead>);

impl fmt::Display for InfHeadCycle {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(")?;
        for s in &self.0 {
            write!(f, "{s}")?;
        }
        write!(f, ")^inf")
    }
}

impl InfHeadCycle {
    fn pop(&mut self) -> LongHead {
        let h = self.0.pop_back().unwrap();
        self.0.push_front(h);
        h
    }

    fn has_wrapping_d(&self) -> bool {
        self.0.back() == Some(&LongHead::B) && self.0.front() == Some(&LongHead::A)
    }

    fn is_even(&self) -> bool {
        let mut out = true;
        for h in &self.0 {
            if *h != LongHead::D {
                out = !out;
            }
        }
        out
    }

    fn double(&mut self) {
        let n = self.0.len();
        for i in 0..n {
            self.0.push_back(self.0[i]);
        }
    }

    fn replace_ba_with_d(&mut self) -> bool {
        use LongHead::*;

        let mut replaced = false;
        let mut n_left = self.0.len();

        while n_left > 0 {
            let s = self.0.pop_back().unwrap();
            if s == A && n_left >= 2 && self.0.back() == Some(&B) {
                self.0.pop_back();
                self.0.push_front(D);
                n_left -= 2;
                replaced = true;
            } else {
                self.0.push_front(s);
                n_left -= 1;
            }
        }
        replaced
    }

    fn propagate_head_periodic(&mut self, s0: &RightSymbol) {
        let mut n = self.0.len();
        let mut s = *s0;

        for _ in 0..n {
            let h = self.0.pop_back().unwrap();
            let (s_new, maybe_h) = apply_head(&h, &s);
            s = s_new;
            if let Some(h_next) = maybe_h {
                self.0.push_front(h_next);
            }
        }
        assert!(s == *s0);
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum RightSymbol {
    S1,
    S2,
    R,
}

impl RightSymbol {
    fn flip(&self) -> RightSymbol {
        use RightSymbol::*;
        match &self {
            S1 => S2,
            S2 => S1,
            R => R,
        }
    }
}

impl fmt::Display for RightSymbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use RightSymbol::*;
        match &self {
            S1 => write!(f, "1"),
            S2 => write!(f, "2"),
            R => write!(f, "$"),
        }
    }
}

#[derive(Clone, Copy)]
enum LongTerm {
    Symbol(RightSymbol),
    Head(LongHead),
}

struct CycleSim {
    cycle: InfHeadCycle,
    near_tape: Vec<LongTerm>,
    end_tape: Vec<RightSymbol>,
    n_cells: u64,
    self_steps: u64,
}

impl fmt::Display for CycleSim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        write!(f, "{} | {}: {} ", self.self_steps, self.n_cells, self.cycle)?;

        for x in &self.near_tape {
            match x {
                LongTerm::Head(h) => {
                    let s0 = format!("{h}");
                    write!(f, "{}", s0.red().bold())?;
                }
                LongTerm::Symbol(s) => {
                    write!(f, "{s}")?;
                }
            }
        }

        for s in self.end_tape.iter().rev() {
            write!(f, "{s}")?;
        }
        Ok(())
    }
}

fn apply_head(h: &LongHead, s: &RightSymbol) -> (RightSymbol, Option<LongHead>) {
    use LongHead::*;
    use RightSymbol::*;
    let next_h = match (h, s) {
        (A, _) => None,
        (B, S1) => Some(D),
        (C, S1) => Some(B),
        (D, S1) => Some(C),
        (B, S2) => Some(C),
        (C, S2) => Some(A),
        (D, S2) => Some(D),
        (_, R) => unimplemented!(),
    };
    let next_s = if *h == D { *s } else { s.flip() };
    (next_s, next_h)
}

impl CycleSim {
    fn new() -> Self {
        use LongHead::*;
        Self {
            cycle: InfHeadCycle(VecDeque::from([C, B])),
            near_tape: Vec::new(),
            end_tape: vec![RightSymbol::R],
            n_cells: 0,
            self_steps: 0,
        }
    }

    fn step(&mut self, keep_runs_together: bool) {
        use LongHead::*;
        use RightSymbol::*;
        if let Some(t) = self.near_tape.pop() {
            match t {
                LongTerm::Symbol(s) => {
                    self.end_tape.push(s);
                    while let Some(LongTerm::Symbol(s2)) = self.near_tape.last() {
                        self.end_tape.push(*s2);
                        self.near_tape.pop();
                    }
                }
                LongTerm::Head(h) => match self.end_tape.last().unwrap() {
                    R => match h {
                        A => self.end_tape.extend_from_slice(&[S2, S2]),
                        B => self.end_tape.push(S2),
                        C => panic!("halt"),
                        D => self.end_tape.extend_from_slice(&[S2, S2, S1, S1]),
                    },
                    S1 | S2 => {
                        let s = self.end_tape.pop().unwrap();
                        let (next_s, next_h) = apply_head(&h, &s);
                        if let Some(nh) = next_h {
                            self.near_tape.push(LongTerm::Symbol(next_s));
                            self.near_tape.push(LongTerm::Head(nh));
                        } else {
                            self.end_tape.push(next_s);
                        }
                    }
                },
            }
        } else {
            // do something with the head cycle
            if !self.cycle.replace_ba_with_d() {
                if self.cycle.has_wrapping_d() || self.end_tape.len() == 1 {
                    self.near_tape.push(LongTerm::Head(self.cycle.pop()));
                } else if keep_runs_together
                    && ((self.cycle.0.front() == Some(&D) && self.cycle.0.back() == Some(&D))
                        || (self.cycle.0.front() == Some(&C) && self.cycle.0.back() == Some(&C)))
                {
                    self.near_tape.push(LongTerm::Head(self.cycle.pop()));
                } else {
                    if self.cycle.is_even() {
                        self.cycle
                            .propagate_head_periodic(&self.end_tape.pop().unwrap());
                        self.n_cells += 1;
                    } else {
                        self.cycle.double();
                    }
                }
            }
        }
        self.self_steps += 1;
    }
}

fn main() {
    let mut sim = CycleSim::new();
    println!("{sim}");

    for i in 1..=1000 {
        sim.step(true);
        println!("{sim}");
    }
}
