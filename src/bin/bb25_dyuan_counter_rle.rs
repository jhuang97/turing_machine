use arbitrary_int::{traits::Integer, u7};
use bitbybit::{bitenum, bitfield};
use std::collections::{BTreeMap, HashMap, VecDeque};
use std::fmt;

#[bitenum(u1, exhaustive = true)]
#[derive(Debug, PartialEq, Eq, Hash)]
enum HeadType {
    A = 0b0,
    B = 0b1,
}

impl fmt::Display for HeadType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        match self {
            Self::A => write!(f, "{}", "A".red().bold()),
            Self::B => write!(f, "{}", "B".red().bold()),
        }
    }
}

#[bitfield(u8)]
#[derive(Debug, PartialEq, Eq, Hash)]
struct Head {
    #[bit(7, rw)]
    t: HeadType,

    #[bits(0..=6, rw)]
    exp: u7,
}

impl Head {
    const fn new(t: HeadType, exp: u8) -> Self {
        Head::builder().with_t(t).with_exp(u7::new(exp)).build()
    }
}

impl fmt::Display for Head {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.exp().as_u8() == 1 {
            write!(f, "{}", self.t())
        } else {
            write!(f, "{}^{}", self.t(), self.exp())
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug, Hash)]
enum TapeSymbol {
    Run(RunType, Exp),
    R,
}

impl fmt::Display for TapeSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            Self::Run(t, exp) => {
                if *exp != 1 {
                    write!(f, "{t}^{exp}")
                } else {
                    write!(f, "{t}")
                }
            }
            Self::R => write!(f, "R"),
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum RunType {
    S13,
    S33,
    S31,
    S11,
}

impl fmt::Display for RunType {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::S13 => write!(f, "13"),
            Self::S33 => write!(f, "33"),
            Self::S31 => write!(f, "31"),
            Self::S11 => write!(f, "11"),
        }
    }
}

type Exp = u8;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum LongSymbol {
    Head(Head),
    Symbol(TapeSymbol),
}

impl fmt::Display for LongSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            Self::Head(h) => write!(f, "{h}"),
            Self::Symbol(ts) => write!(f, "{ts}"),
        }
    }
}

#[derive(Clone)]
struct VecCycleIterator<T>
where
    T: Clone,
{
    seq: Vec<T>,
    idx: usize,
}

impl<T> VecCycleIterator<T>
where
    T: Clone,
{
    fn new(seq: Vec<T>) -> Self {
        Self { seq, idx: 0 }
    }

    fn peek(&self) -> &T {
        &self.seq[self.idx]
    }

    fn len(&self) -> usize {
        self.seq.len()
    }

    fn replace(&mut self, new_seq: Vec<T>) {
        self.seq = new_seq;
        self.idx = 0;
    }
}

impl<T> Iterator for VecCycleIterator<T>
where
    T: Clone,
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        let current = self.seq[self.idx].clone();
        self.idx = (self.idx + 1) % self.seq.len();
        Some(current)
    }
}

struct CycleInfo {
    emitted_heads: Vec<Head>,
    target_symbol: TapeSymbol,
    /// remaining head runs in the current cycle
    n_remaining: usize,
}

struct LongSim {
    head_generator: VecCycleIterator<Head>,
    n_head_gen: u64,
    cycle_len: usize,

    /// head_generator feeds into front of near_tape, back of near_tape connects with end_tape
    near_tape: VecDeque<LongSymbol>,

    end_tape: Vec<TapeSymbol>,
    cycle_info: Option<CycleInfo>,
    head_steps: u64,
    self_move_steps: u64,
}

impl LongSim {
    fn new() -> Self {
        const HEAD_SEQ: [Head; 2] = [Head::new(HeadType::A, 1), Head::new(HeadType::B, 1)];
        let head_generator = VecCycleIterator::new(Vec::from(HEAD_SEQ));

        let end_tape = {
            use RunType::*;
            use TapeSymbol::*;
            let mut tape = vec![
                Run(S31, 2),
                Run(S13, 2),
                Run(S11, 1),
                Run(S13, 4),
                Run(S11, 1),
                Run(S31, 1),
                Run(S13, 4),
                R,
            ];
            tape.reverse();
            tape
        };

        Self {
            head_generator,
            n_head_gen: 0,
            cycle_len: HEAD_SEQ.len(),
            near_tape: VecDeque::new(),
            end_tape,
            cycle_info: None,
            head_steps: 0,
            self_move_steps: 0,
        }
    }

    fn new_for_cycle(head_generator: VecCycleIterator<Head>, next_symbol: TapeSymbol) -> Self {
        let cycle_len = head_generator.len();
        let end_tape = vec![next_symbol];
        let cycle_info = CycleInfo {
            emitted_heads: Vec::new(),
            target_symbol: next_symbol,
            n_remaining: cycle_len,
        };
        Self {
            head_generator,
            n_head_gen: 0,
            cycle_len,
            near_tape: VecDeque::new(),
            end_tape,
            cycle_info: Some(cycle_info),
            head_steps: 0,
            self_move_steps: 0,
        }
    }

    fn cycle_completed(&self) -> bool {
        let Some(c_info) = &self.cycle_info else {
            return false;
        };
        if c_info.n_remaining != 0 {
            return false;
        }
        if self.near_tape.len() == 1
            && let Some(LongSymbol::Symbol(s)) = self.near_tape.front()
            && *s == c_info.target_symbol
        {
            return true;
        }
        self.near_tape.len() == 0
            && self.end_tape.len() == 1
            && *self.end_tape.first().unwrap() == c_info.target_symbol
    }

    /// decrements a run of tape symbol on `end_tape`
    fn decrement_symbol(&mut self, st: RunType) {
        if let Some(TapeSymbol::Run(st0, m)) = self.end_tape.last_mut() {
            assert!(st == *st0);
            assert!(*m > 0);
            if *m > 1 {
                *m -= 1;
            } else {
                self.end_tape.pop();
            }
        } else {
            unreachable!()
        }
    }

    fn push_symbol_near(&mut self, st: RunType, madd: Exp) {
        use LongSymbol::*;
        use TapeSymbol::Run;
        if let Some(Symbol(Run(st0, m))) = self.near_tape.back_mut()
            && *st0 == st
        {
            *m += madd;
        } else {
            self.near_tape.push_back(Symbol(Run(st, madd)));
        }
    }

    fn push_symbol_end(&mut self, ts: TapeSymbol) {
        use TapeSymbol::*;
        if let Some(Run(st0, m0)) = self.end_tape.last_mut()
            && let Run(st1, m1) = ts
            && *st0 == st1
        {
            *m0 += m1;
        } else {
            self.end_tape.push(ts);
        }
    }

    /// handles case where `nadd` is 0, does not push runs of length 0
    fn push_head(&mut self, t: HeadType, nadd: u8) {
        if nadd == 0 {
            return;
        }
        if self.end_tape.is_empty()
            && let Some(c) = &mut self.cycle_info
        {
            if let Some(h0) = c.emitted_heads.last_mut()
                && h0.t() == t
            {
                h0.set_exp(h0.exp() + u7::new(nadd));
            } else {
                c.emitted_heads.push(Head::new(t, nadd));
            }
        } else {
            if let Some(LongSymbol::Head(h0)) = self.near_tape.back_mut()
                && h0.t() == t
            {
                h0.set_exp(h0.exp() + u7::new(nadd));
            } else {
                self.near_tape
                    .push_back(LongSymbol::Head(Head::new(t, nadd)));
            }
        }
    }

    fn step(&mut self, count_cycle_steps: bool) -> bool {
        use HeadType::*;
        use LongSymbol::*;
        use RunType::*;
        use TapeSymbol::*;

        let is_head_step = match (self.near_tape.back(), self.end_tape.last()) {
            (None, _) => {
                let n_heads = if count_cycle_steps && let Some(c_info) = &mut self.cycle_info {
                    if c_info.n_remaining == 0 {
                        c_info.n_remaining = self.cycle_len;
                    }

                    const MAX_N_HEADS: usize = 1000000;
                    let n_heads = self.cycle_len.min(MAX_N_HEADS).min(c_info.n_remaining);
                    c_info.n_remaining -= n_heads;
                    n_heads
                } else {
                    1
                };
                for _ in 0..n_heads {
                    self.near_tape
                        .push_front(Head(self.head_generator.next().unwrap()));
                    self.n_head_gen += 1;
                }
                true
            }
            (Some(Symbol(s)), _) => {
                self.push_symbol_end(*s);
                self.near_tape.pop_back();
                false
            }
            (Some(Head(head)), Some(symb)) => {
                let head = *head;
                self.near_tape.pop_back();
                match (head.t(), symb) {
                    // A^2n   13 -> 13 A^n
                    // A^2n+1 13 -> 33 A^n
                    (A, Run(S13, _)) => {
                        let n = head.exp().as_u8();
                        self.decrement_symbol(S13);
                        if n % 2 == 0 {
                            self.push_symbol_near(S13, 1);
                        } else {
                            self.push_symbol_near(S33, 1);
                        }
                        self.push_head(A, n / 2);
                    }
                    // A 33^m -> 13^m A
                    (A, Run(S33, m0)) if head.exp().as_u8() == 1 => {
                        let m = *m0;
                        self.end_tape.pop();
                        self.push_symbol_near(S13, m);
                        self.push_head(A, 1);
                    }
                    // A^2n   33 -> 33 A^n
                    // A^2n+1 33 -> 13 A^n+1
                    (A, Run(S33, _)) => {
                        let n = head.exp().as_u8();
                        self.decrement_symbol(S33);
                        if n % 2 == 0 {
                            self.push_symbol_near(S33, 1);
                            self.push_head(A, n / 2);
                        } else {
                            self.push_symbol_near(S13, 1);
                            self.push_head(A, n / 2 + 1);
                        }
                    }
                    (A, Run(S31, m0)) => {
                        let m = *m0;
                        let n = head.exp().as_u8();
                        if n % 2 == 0 {
                            // A^2n 31 -> 31 A^2n (can be shift rule)
                            self.end_tape.pop();
                            self.push_symbol_near(S31, m);
                            self.push_head(A, n);
                        } else {
                            // A^2n+1 31 -> 11 A^2n+2
                            self.decrement_symbol(S31);
                            self.push_symbol_near(S11, 1);
                            self.push_head(A, n + 1);
                        }
                    }
                    (A, Run(S11, m0)) => {
                        let m = *m0;
                        let n = head.exp().as_u8();
                        if n % 2 == 0 {
                            // A^2n 11 -> 11 A^2n (can be shift rule)
                            self.end_tape.pop();
                            self.push_symbol_near(S11, m);
                            self.push_head(A, n);
                        } else {
                            // A^2n+1 11 -> 31 A^2n
                            self.decrement_symbol(S11);
                            self.push_symbol_near(S31, 1);
                            self.push_head(A, n - 1);
                        }
                    }
                    (A, R) => {
                        unimplemented!("A R");
                    }
                    // shift rules:
                    // B^n 13 -> 13 B^n
                    // B^n 11 -> 11 B^n
                    (B, Run(t0 @ S13 | t0 @ S11, m0)) => {
                        let t = *t0;
                        let m = *m0;
                        let n = head.exp().as_u8();
                        self.end_tape.pop();
                        self.push_symbol_near(t, m);
                        self.push_head(B, n);
                    }
                    // B 33^m -> 31^m B
                    (B, Run(S33, m0)) if head.exp().as_u8() == 1 => {
                        let m = *m0;
                        self.end_tape.pop();
                        self.push_symbol_near(S31, m);
                        self.push_head(B, 1);
                    }
                    (B, Run(S33, _)) => {
                        let n = head.exp().as_u8();
                        self.decrement_symbol(S33);
                        if n % 2 == 0 {
                            // B^2n 33 -> 33 B^n
                            self.push_symbol_near(S33, 1);
                            self.push_head(B, n / 2);
                        } else {
                            // B^2n+1 33 -> 31 B^n+1
                            self.push_symbol_near(S31, 1);
                            self.push_head(B, n / 2 + 1);
                        }
                    }
                    // B^2n   31 -> 31 B^n
                    // B^2n+1 31 -> 33 B^n
                    (B, Run(S31, _)) => {
                        let n = head.exp().as_u8();
                        self.decrement_symbol(S31);
                        if n % 2 == 0 {
                            self.push_symbol_near(S31, 1);
                        } else {
                            self.push_symbol_near(S33, 1);
                        }
                        self.push_head(B, n / 2);
                    }
                    // B^n 332$ -> 13^n 332$
                    (B, R) => {
                        let n = head.exp().as_u8();
                        self.end_tape.push(Run(S13, n));
                    }
                }
                true
            }
            _ => unreachable!(),
        };
        if is_head_step {
            self.head_steps += 1;
        } else {
            self.self_move_steps += 1;
        }
        is_head_step
    }

    fn push_cycle(&mut self) {
        use RunType::*;
        use TapeSymbol::*;
        let next_symbol = 's: loop {
            if self.near_tape.is_empty() {
                match self.end_tape.last() {
                    Some(Run(st0, _)) => {
                        let st = *st0;
                        self.decrement_symbol(st);
                        break 's st;
                    }
                    Some(R) => {
                        println!("reached R; next: {}", self.head_generator.peek());
                        self.step(false);
                    }
                    None => {
                        self.step(false);
                    }
                }
            } else {
                self.step(false);
            }
        };

        let mut inner_sim =
            LongSim::new_for_cycle(self.head_generator.clone(), Run(next_symbol, 1));
        loop {
            if inner_sim.step(true) {
                //     println!("{inner_sim}");
            }
            if inner_sim.cycle_completed() {
                let cycle = inner_sim.cycle_info.unwrap().emitted_heads;

                print!("{} ", cycle.len());
                if cycle.len() < 100 {
                    for s in &cycle {
                        print!("{s} ");
                    }
                }
                println!();
                print_run_histogram(&cycle);

                self.cycle_len = cycle.len();
                self.head_generator.replace(cycle);
                break;
            }
        }
    }
}

impl fmt::Display for LongSim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        self.head_steps.fmt(f)?;

        if let Some(c_info) = &self.cycle_info {
            write!(f, ": {}^-1 ", c_info.target_symbol)?;
            if c_info.n_remaining > 0 {
                write!(f, "...{}... ", c_info.n_remaining)?;
            }
        } else {
            write!(
                f,
                ": ({}) ...{} ",
                self.head_generator.len(),
                self.head_generator.peek()
            )?;
        }

        const LEFT_PRINT_THRESHOLD: usize = 20;
        let l_th = LEFT_PRINT_THRESHOLD / 2;
        if self.near_tape.len() <= LEFT_PRINT_THRESHOLD {
            for symb in &self.near_tape {
                write!(f, "{} ", symb)?;
            }
        } else {
            let mut iter = self.near_tape.iter();
            for _ in 0..l_th {
                write!(f, "{} ", iter.next().unwrap())?;
            }
            write!(
                f,
                "...{} terms... ",
                self.near_tape.len() - LEFT_PRINT_THRESHOLD
            )?;
            for i in self.near_tape.len() - l_th..self.near_tape.len() {
                write!(f, "{} ", self.near_tape.get(i).unwrap())?;
            }
        }
        // write!(f, " ")?;
        const RIGHT_PRINT_THRESHOLD: usize = 65;
        let r_th = RIGHT_PRINT_THRESHOLD / 2;
        if self.end_tape.len() <= RIGHT_PRINT_THRESHOLD {
            for symb in self.end_tape.iter().rev() {
                write!(f, " {}", symb)?;
            }
        } else {
            for symb in self.end_tape[self.end_tape.len() - r_th..].iter().rev() {
                write!(f, " {}", symb)?;
            }
            write!(
                f,
                " ...{} terms...",
                self.end_tape.len() - RIGHT_PRINT_THRESHOLD
            )?;
            for symb in self.end_tape[..r_th].iter().rev() {
                write!(f, " {}", symb)?;
            }
        }

        if let Some(c_info) = &self.cycle_info {
            write!(f, " ")?;
            for symb in c_info.emitted_heads.iter().rev() {
                write!(f, " {}", symb)?;
            }
        }
        Ok(())
    }
}

fn try_bitfield() {
    let mut h = Head::new(HeadType::A, 15);
    println!("{} {}", h, h.exp().as_u8());
    h.set_t(HeadType::B);
    h.set_exp(u7::new(20));
    println!("{} {}", h, h.exp().as_u8());
    h.set_exp(u7::new(1));
    println!("{} {}", h, h.exp().as_u8());
}

fn try_get_cycle() {
    let mut sim = {
        use HeadType::*;
        use RunType::*;
        use TapeSymbol::*;
        let head_seq = vec![Head::new(A, 1), Head::new(B, 1)];
        // let mut head_seq = Vec::new();
        // for _ in 0..26 {
        //     head_seq.push(Head::new(A, 1));
        //     head_seq.push(Head::new(B, 1));
        // }
        LongSim::new_for_cycle(VecCycleIterator::new(head_seq), Run(S31, 1))
    };
    loop {
        if sim.step(true) {
            println!("{sim}");
        }
        if sim.cycle_completed() {
            let cycle = sim.cycle_info.unwrap().emitted_heads;
            for s in &cycle {
                print!("{s} ");
            }
            println!();
            break;
        }
    }
}

fn print_run_histogram(v: &Vec<Head>) {
    let mut histogram: HashMap<HeadType, BTreeMap<u8, usize>> = HashMap::new();

    for r in v {
        *histogram
            .entry(r.t())
            .or_default()
            .entry(r.exp().as_u8())
            .or_default() += 1;
    }

    for symbol in [HeadType::A, HeadType::B] {
        let sub_hist = histogram.get(&symbol).unwrap();
        print!("{symbol}:  ");
        let mut n_runs = 0;
        for (run_length, count) in sub_hist {
            print!("{run_length}: {count}, ");
            n_runs += count;
        }
        println!(" {n_runs} runs");
    }
}

fn is_pow2_or_0(n: u64) -> bool {
    (n & (n - 1)) == 0
}

fn main() {
    // let mut sim = LongSim::new();
    // println!("{sim}");
    // // let max_steps = 1000000000000u64;
    // // //                    516000000000
    // // let max_steps = 1000000;
    // let max_steps = 100000;
    // // let max_steps = 1000;
    // // let max_steps = 100;
    // for i in 0..=max_steps {
    //     if sim.step(true)
    //     //         // && sim.end_tape.len() <= 3
    //     // //         && (sim.end_tape.len() == 8 || sim.end_tape.len() == 1)
    //     //     // && sim.head_steps % 10000000 == 0
    //     {
    //         println!("{sim}");
    //     }
    // }

    // try_get_cycle();
    //

    let mut sim = LongSim::new();
    // sim.end_tape = vec![TapeSymbol::R, TapeSymbol::Run(RunType::S13, 2)];
    println!("{sim}");

    // // pushing cycle 20 times appears to consume 4-5 GB of RAM
    for i in 0..20 {
        sim.push_cycle();
        println!("{sim}");
    }

    let max_steps = 1000000000000u64;
    // //                    516000000000
    // let max_steps = 1000000;
    // let max_steps = 1000;
    // let max_steps = 100;
    for i in 0..=max_steps {
        if sim.step(true)
        //&& sim.end_tape.len() <= 3
        // //         && (sim.end_tape.len() == 8 || sim.end_tape.len() == 1)
        // && sim.head_steps % 1000000000 == 0
        {
            // println!("{sim}");
            //
            let n = sim.head_steps;
            if is_pow2_or_0(n) || (n % 3 == 0 && is_pow2_or_0(n / 3)) {
                if let [TapeSymbol::R, TapeSymbol::Run(RunType::S13, k), ..] =
                    sim.end_tape.as_slice()
                {
                    println!("{n} {k}");
                }
            }
        }
    }
}
