use std::{
    collections::{BTreeMap, HashMap, VecDeque},
    fmt,
    hash::Hash,
    usize,
};

type Exp = u8;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum LongSymbol {
    Ha,
    Hb,
    S13(Exp),
    S33,
    S31,
    S11,
    R,
}

impl fmt::Display for LongSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        match self {
            Self::Ha => write!(f, "{}", "A".red().bold()),
            Self::Hb => write!(f, "{}", "B".red().bold()),
            Self::S13(n) => {
                if *n > 1 {
                    write!(f, " 13^{n}")
                } else {
                    write!(f, " 13")
                }
            }
            Self::S33 => write!(f, " 33"),
            Self::S31 => write!(f, " 31"),
            Self::S11 => write!(f, " 11"),
            Self::R => write!(f, "{}", " R".bold()),
        }
    }
}

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
    emitted_heads: Vec<LongSymbol>,
    target_symbol: LongSymbol,
}

struct LongSim {
    head_generator: VecCycleIterator<LongSymbol>,
    n_head_gen: u64,
    cycle_len: usize,

    /// head_generator feeds into front of near_tape, back of near_tape connects with end_tape
    near_tape: VecDeque<LongSymbol>,

    /// must not contain heads
    end_tape: Vec<LongSymbol>,
    cycle_info: Option<CycleInfo>,
    head_steps: u64,
    self_move_steps: u64,
}

impl LongSim {
    fn new() -> Self {
        const HEAD_SEQ: [LongSymbol; 2] = [LongSymbol::Ha, LongSymbol::Hb];
        let head_generator = VecCycleIterator::new(Vec::from(HEAD_SEQ));

        let end_tape = {
            use LongSymbol::*;
            let mut tape = vec![S31, S31, S13(2), S11, S13(4), S11, S31, S13(4), R];
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

    fn new_for_cycle(head_seq: Vec<LongSymbol>, next_symbol: LongSymbol) -> Self {
        let cycle_len = head_seq.len();
        let head_generator = VecCycleIterator::new(head_seq);
        let end_tape = vec![next_symbol];
        let cycle_info = CycleInfo {
            emitted_heads: Vec::new(),
            target_symbol: next_symbol,
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

    fn new_for_check(
        head: LongSymbol,
        n_head: usize,
        block0: LongSymbol,
        block1: LongSymbol,
    ) -> Self {
        let cycle_len = n_head;
        let mut head_seq = Vec::new();
        for _ in 0..n_head {
            head_seq.push(head);
        }
        let head_generator = VecCycleIterator::new(head_seq);
        let end_tape = vec![block0];
        let cycle_info = CycleInfo {
            emitted_heads: Vec::new(),
            target_symbol: block1,
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
        if self.near_tape.len() == 1 && *self.near_tape.front().unwrap() == c_info.target_symbol {
            return true;
        }
        self.near_tape.len() == 0
            && self.end_tape.len() == 1
            && *self.end_tape.first().unwrap() == c_info.target_symbol
    }

    fn push_head(&mut self, head: LongSymbol) {
        if self.end_tape.is_empty()
            && let Some(c) = &mut self.cycle_info
        {
            c.emitted_heads.push(head);
        } else {
            self.near_tape.push_back(head);
        }
    }

    fn step(&mut self) -> bool {
        use LongSymbol::*;
        let is_head_step = match (self.near_tape.back(), self.end_tape.last()) {
            (None, _) => {
                let n_heads = if self.cycle_info.is_some() {
                    self.cycle_len
                } else {
                    1
                };
                for _ in 0..n_heads {
                    self.near_tape
                        .push_front(self.head_generator.next().unwrap());
                    self.n_head_gen += 1;
                }
                true
            }
            // A 13 -> 33
            (Some(Ha), Some(S13(n0))) => {
                let n = *n0;
                self.near_tape.pop_back();
                self.end_tape.pop();
                if n > 1 {
                    self.end_tape.push(S13(n - 1));
                }
                self.end_tape.push(S33);
                true
            }
            // A 33 -> 13 A
            (Some(Ha), Some(S33)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                if let Some(S13(n)) = self.near_tape.back_mut() {
                    *n += 1;
                } else {
                    self.near_tape.push_back(S13(1));
                }
                self.push_head(Ha);
                true
            }
            // A 31 -> 11 A A
            (Some(Ha), Some(S31)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S11);
                self.push_head(Ha);
                self.push_head(Ha);
                true
            }
            // A 11 -> 31
            (Some(Ha), Some(S11)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.end_tape.push(S31);
                true
            }
            // A 332$ -> ---
            (Some(Ha), Some(R)) => {
                self.debug_print();
                unimplemented!();
            }
            // B 13 -> 13 B
            (Some(Hb), Some(S13(m0))) => {
                let m = *m0;
                self.near_tape.pop_back();
                self.end_tape.pop();
                if let Some(S13(n)) = self.near_tape.back_mut() {
                    *n += m;
                } else {
                    self.near_tape.push_back(S13(m));
                }
                self.push_head(Hb);
                true
            }
            // B 33 -> 31 B
            (Some(Hb), Some(S33)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S31);
                self.push_head(Hb);
                true
            }
            // B 31 -> 33
            (Some(Hb), Some(S31)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.end_tape.push(S33);
                true
            }
            // B 11 -> 11 B
            (Some(Hb), Some(S11)) => {
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.near_tape.push_back(S11);
                self.push_head(Hb);
                true
            }
            // B 332$ -> 13 332$
            (Some(Hb), Some(R)) => {
                self.near_tape.pop_back();
                self.end_tape.push(S13(1));
                true
            }
            (Some(S13(m0)), Some(S13(n0))) => {
                let s = *m0 + *n0;
                self.near_tape.pop_back();
                self.end_tape.pop();
                self.end_tape.push(S13(s));
                false
            }
            (Some(_), _) => {
                self.end_tape.push(self.near_tape.pop_back().unwrap());
                false
            }
        };
        if is_head_step {
            self.head_steps += 1;
        } else {
            self.self_move_steps += 1;
        }
        is_head_step
    }

    fn debug_print(&self) {
        let cell_count = self
            .near_tape
            .iter()
            .filter(|&&s| s != LongSymbol::Ha && s != LongSymbol::Hb)
            .count();
        eprintln!("{self}, {cell_count} cells");
    }
}

impl fmt::Display for LongSim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        self.head_steps.fmt(f)?;

        if let Some(c_info) = &self.cycle_info {
            write!(f, "{}^-1 ", c_info.target_symbol)?;
        } else {
            write!(f, ": ...{} ", self.head_generator.peek())?;
        }

        const LEFT_PRINT_THRESHOLD: usize = 8;
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
            write!(
                f,
                " ...{} terms... ",
                self.near_tape.len() - LEFT_PRINT_THRESHOLD
            )?;
            for i in self.near_tape.len() - l_th..self.near_tape.len() {
                write!(f, "{}", self.near_tape.get(i).unwrap())?;
            }
        }
        // write!(f, " ")?;
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
                f,
                " ...{} terms... ",
                self.end_tape.len() - RIGHT_PRINT_THRESHOLD
            )?;
            for symb in self.end_tape[..r_th].iter().rev() {
                write!(f, "{}", symb)?;
            }
        }

        if let Some(c_info) = &self.cycle_info {
            write!(f, " ")?;
            for symb in c_info.emitted_heads.iter().rev() {
                write!(f, "{}", symb)?;
            }
        }
        Ok(())
    }
}

fn check_head_rle(
    head: LongSymbol,
    n_in: usize,
    block0: LongSymbol,
    block1: LongSymbol,
    n_out: usize,
) -> bool {
    let mut sim = LongSim::new_for_check(head, n_in, block0, block1);
    loop {
        sim.step();
        // println!("{sim}");
        // println!(
        //     "{sim} {} {} {} {}",
        //     sim.n_head_gen,
        //     sim.cycle_len,
        //     sim.near_tape.len(),
        //     sim.end_tape.len()
        // );
        if sim.n_head_gen == sim.cycle_len as u64 && sim.cycle_completed() {
            println!("complete {head}^{n_in} -> {sim}");
            if let Some(c_info) = &sim.cycle_info {
                let out_heads = &c_info.emitted_heads;
                if out_heads.len() == n_out {
                    if out_heads.iter().all(|h| *h == head) {
                        return true;
                    }
                }
            }
        } else if sim.n_head_gen > sim.cycle_len as u64 {
            println!("past {sim} {} {}", sim.n_head_gen, sim.cycle_len);
            return false;
        }
    }
}

fn check_head_rle_rules(n_max: usize) {
    use LongSymbol::*;
    for n in 1..=n_max {
        assert!(check_head_rle(Ha, 2 * n, S13(1), S13(1), n));
        assert!(check_head_rle(Ha, 2 * n, S33, S33, n));
        assert!(check_head_rle(Ha, 2 * n, S31, S31, 2 * n));
        assert!(check_head_rle(Ha, 2 * n, S11, S11, 2 * n));

        assert!(check_head_rle(Hb, n, S13(1), S13(1), n));
        assert!(check_head_rle(Hb, 2 * n, S33, S33, n));
        assert!(check_head_rle(Hb, 2 * n, S31, S31, n));
        assert!(check_head_rle(Hb, n, S11, S11, n));
    }
    for n in 0..=n_max {
        assert!(check_head_rle(Ha, 2 * n + 1, S13(1), S33, n));
        assert!(check_head_rle(Ha, 2 * n + 1, S33, S13(1), n + 1));
        assert!(check_head_rle(Ha, 2 * n + 1, S31, S11, 2 * n + 2));
        assert!(check_head_rle(Ha, 2 * n + 1, S11, S31, 2 * n));

        assert!(check_head_rle(Hb, 2 * n + 1, S33, S31, n + 1));
        assert!(check_head_rle(Hb, 2 * n + 1, S31, S33, n));
    }
}

fn print_run_histogram(v: &Vec<LongSymbol>) {
    let mut run_symbol = v[0];
    let mut run_count: usize = 1;
    let mut histogram: HashMap<LongSymbol, BTreeMap<usize, usize>> = HashMap::new();

    for s in &v[1..] {
        if *s == run_symbol {
            run_count += 1;
        } else {
            *histogram
                .entry(run_symbol)
                .or_default()
                .entry(run_count)
                .or_default() += 1;
            run_symbol = *s;
            run_count = 1;
        }
    }
    *histogram
        .entry(run_symbol)
        .or_default()
        .entry(run_count)
        .or_default() += 1;

    for symbol in [LongSymbol::Ha, LongSymbol::Hb] {
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

fn try_pushing_head_cycle() {
    let mut cycle = vec![LongSymbol::Ha, LongSymbol::Hb];
    let mut end_tape = {
        use LongSymbol::*;
        let mut tape = vec![S31, S31, S13(2), S11, S13(4), S11, S31, S13(4), R];
        tape.reverse();
        tape
    };
    let max_inner_steps = 100000000000u64;
    let max_outer_steps = 16;
    let mut n_outer_steps = 0;
    loop {
        let next_symbol = {
            use LongSymbol::*;
            match end_tape.pop() {
                Some(n @ S11 | n @ S33 | n @ S31) => n,
                Some(S13(1)) => S13(1),
                Some(S13(n @ 2..)) => {
                    end_tape.push(S13(n - 1));
                    S13(1)
                }
                Some(R) => {
                    println!("reached 332$");

                    for i in (0..=300).rev() {
                        print!("{}", cycle[i]);
                    }
                    println!();
                    let mut n_A = 0;
                    let mut n_B = 0;
                    for &n in &cycle {
                        if n == Ha {
                            n_A += 1;
                        } else if n == Hb {
                            n_B += 1;
                        }
                    }
                    println!("# A: {}, # B: {}", n_A, n_B);
                    match cycle.first() {
                        Some(Ha) => {
                            println!("A reached R!");
                            break;
                        }
                        Some(Hb) => {
                            end_tape.push(R);
                            cycle.remove(0);
                            cycle.push(Hb);
                            S13(1)
                        }
                        None => unreachable!(),
                        _ => unimplemented!(),
                    }
                }
                x @ _ => {
                    eprintln!("{x:?}");
                    unimplemented!()
                }
            }
        };

        {
            let mut sim = LongSim::new_for_cycle(cycle.clone(), next_symbol);
            let mut i = 0;
            loop {
                if sim.step() {
                    // println!("{sim}");
                }
                if sim.cycle_completed() {
                    cycle = sim.cycle_info.unwrap().emitted_heads;
                    break;
                } else if i >= max_inner_steps {
                    break;
                }
                i += 1;
            }
            if i >= max_inner_steps {
                println!("too many steps");
                break;
            } else {
                // the cycle is good, print some info about it
                print!("{} ", cycle.len());
                if cycle.len() < 550 {
                    for s in &cycle {
                        print!("{s}");
                    }
                }
                println!();
                print_run_histogram(&cycle);
                println!();
            }
        }

        n_outer_steps += 1;
        if n_outer_steps > max_outer_steps {
            break;
        }
    }
}

fn main() {
    let mut sim = LongSim::new();
    println!("{sim}");

    // let max_steps = 1000000000000u64;
    // //                    516000000000
    let max_steps = 100000;
    // let max_steps = 1000;
    // let max_steps = 100;
    for i in 0..=max_steps {
        if sim.step()
        //         // && sim.end_tape.len() <= 3
        // //         && (sim.end_tape.len() == 8 || sim.end_tape.len() == 1)
        //     // && sim.head_steps % 10000000 == 0
        {
            println!("{sim}");
        }
    }

    // try_pushing_head_cycle();

    // check_head_rle_rules(10);

    // let size_type = std::mem::size_of::<LongSymbol>();
    // println!("Size: {} bytes", size_type);
}
