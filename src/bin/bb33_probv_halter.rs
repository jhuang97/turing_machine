use std::collections::HashMap;
use std::iter::Cycle;
use std::{env, str::FromStr};
use std::{fmt, fs, io, u64};
use npyz::{TypeStr, WriterBuilder};
use syn::token::Mod;
use turing_machine::{check_transition_rule, BasicSimulator, BasicStepInfo, CheckerVerbosity, ConfigTransitionRule, State, Symbol, TMDirection, TuringMachine};
use strum_macros::Display;
use num_rational::Ratio;

fn check_text_config_transition_rules(tm: &TuringMachine, rules_txt: &str) {
    let lines = rules_txt.lines().filter(|s| s.len() > 1);
    for line in lines {
        let rule = ConfigTransitionRule::from_str(line).unwrap();

        let res = check_transition_rule(rule, tm, CheckerVerbosity::All);
        print!("{line}");
        match res {
            Ok(n_steps) => println!(" --- {n_steps} step(s)"),
            Err(err) => println!(" {err:?}"),
        }
    }
}

fn run_basic_sim<F>(tm: &TuringMachine, n_steps: u64, filter: F)
    where F: Fn(&BasicSimulator) -> bool
{
    let mut sim = BasicSimulator::new(tm.clone());
    println!("{}", sim.display_directed_head());
    for _ in 0..n_steps {
        let BasicStepInfo { halted, record} = sim.step();
        if filter(&sim) {
            println!("{}", sim.display_directed_head());
        }
        if halted {
            return;
        }
    }
}

type Num = u128;
type SNum = i128;
const ONE: SNum = 1;
const TWO: SNum = 2;
const THREE: SNum = 3;

#[derive(Clone, Copy)]
enum AacState {
    A(Num, Num),
    Halt(Num)
}

#[derive(Display, Debug, PartialEq, Eq, Clone, Copy)]
#[strum(serialize_all = "snake_case")]
enum AacRule {
    A,
    B,
    C,
    D,
    E,
    F,
    G,
    H,
    I,
    J
}

#[derive(Default, PartialEq, Eq)]
struct RuleSequence(Vec<(AacRule, u32)>);

impl RuleSequence {
    fn push(&mut self, rule: AacRule) {
        if let Some((r, exp)) = self.0.last_mut() {
            if rule == *r {
                *exp += 1;
            } else {
                self.0.push((rule, 1));
            }
        } else {
            self.0.push((rule, 1));
        }
    }
}

impl fmt::Display for RuleSequence {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for (rule, exp) in &self.0 {
            write!(f, "{}", rule)?;
            if *exp > 1 {
                write!(f, "{}", exp)?;
            }
        }
        Ok(())
    }
}

struct AacSimulator {
    state: AacState,
    aac_steps: Num,
    a1_steps: Num,
}

impl AacSimulator {
    pub fn new() -> Self {
        AacSimulator { state: AacState::A(0, 1), aac_steps: 0, a1_steps: 0 }
    }

    pub fn step(&mut self) -> bool {
        use AacState::*;
        self.state = if let A(a, c) = &self.state {
            self.aac_steps += 1;
            if c % 2 == 0 {
                if c >= a {
                    if a % 2 == 0 { Halt(a/2 + c + 4) } // g
                    else { A(3*a, c-a+4) }              // i
                } else {
                    A(a-c-1, 3*c/2 + 2) // a
                }
            } else {
                if c >= a {
                    if a % 2 == 0 { A(1, a/2 + c + 2) } // h
                    else { A(3*a + 2, c - a + 1) }      // j
                } else {
                    if c + 1 == *a { Halt(3 * (c-1) / 2 + 4) } // f
                    else { // c <= a - 2
                        if c % 4 == 1 { 
                            A(a - c - 2, 3 * (c - 1)/2 + 5) // b
                        } else { // c == 3 (mod 4)
                            if c + 2 == *a {
                                A(3*c + 8, 1) // e
                            } else if c + 3 == *a {
                                Halt(3 * (c-1) / 2 + 7) // d
                            } else { // c <= a-4
                                A(a - c - 4, 3*(c - 1)/2 + 8) // c
                            }
                        }
                    }
                }
            }
        } else {
            return true;
        };
        if matches!(&self.state, A(1, _)) {
            self.a1_steps += 1;
        }
        matches!(&self.state, Halt(_))
    }

    pub fn step_save_rule(&mut self) -> Option<AacRule> {
        use AacRule::*;
        use AacState::Halt;
        let (new_state, rule) = if let AacState::A(a, c) = &self.state {
            self.aac_steps += 1;
            if c % 2 == 0 {
                if c >= a {
                    if a % 2 == 0 { (Halt(a/2 + c + 4), G) }
                    else { (AacState::A(3*a, c-a+4), I) }
                } else {
                    (AacState::A(a-c-1, 3*c/2 + 2), A)
                }
            } else {
                if c >= a {
                    if a % 2 == 0 { (AacState::A(1, a/2 + c + 2), H) }
                    else { (AacState::A(3*a + 2, c - a + 1), J) }
                } else {
                    if c + 1 == *a { (Halt(3 * (c-1) / 2 + 4), F) }
                    else { // c <= a - 2
                        if c % 4 == 1 { 
                            (AacState::A(a - c - 2, 3 * (c - 1)/2 + 5), B)
                        } else { // c == 3 (mod 4)
                            if c + 2 == *a {
                                (AacState::A(3*c + 8, 1), E)
                            } else if c + 3 == *a {
                                (Halt(3 * (c-1) / 2 + 7), D)
                            } else { // c <= a-4
                                (AacState::A(a - c - 4, 3*(c - 1)/2 + 8), C)
                            }
                        }
                    }
                }
            }
        } else {
            return None;
        };
        self.state = new_state;

        if matches!(&self.state, AacState::A(1, _)) {
            self.a1_steps += 1;
        }
        Some(rule)
    }
}

impl fmt::Display for AacSimulator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.a1_steps.fmt(f)?;
        write!(f, " | ")?;
        self.aac_steps.fmt(f)?;
        write!(f, " | ")?;
        match self.state {
            AacState::A(a, c) => {
                write!(f, "A(")?;
                a.fmt(f)?;
                write!(f, ", ")?;
                c.fmt(f)?;
                write!(f, ")")?;
            },
            AacState::Halt(n) => {
                write!(f, "Halt(")?;
                n.fmt(f)?;
                write!(f, ")")?;
            }
        }
        Ok(())
    }
}

fn get_delta_c(c0: Num) -> Option<Num> {
    let mut a_sim = AacSimulator { state: AacState::A(1, c0), aac_steps: 0, a1_steps: 0 };

    loop {
        a_sim.step();
        match a_sim.state {
            AacState::Halt(_) => return None,
            AacState::A(1, c_new) => return Some(c_new - c0),
            _ => (),
        }
    }
}

fn get_rule_sequence(c0: Num) -> RuleSequence {
    let mut a_sim = AacSimulator { state: AacState::A(1, c0), aac_steps: 0, a1_steps: 0 };

    let mut seq: RuleSequence = RuleSequence::default();

    loop {
        if let Some(r) = a_sim.step_save_rule() {
            seq.push(r);
        }
        match a_sim.state {
            AacState::Halt(_) => break,
            AacState::A(1, _) => break,
            _ => (),
        }
    }
    seq
}

fn get_rule_ac_sequence(c0: Num) -> (RuleSequence, Vec<AacState>) {
    let mut a_sim = AacSimulator { state: AacState::A(1, c0), aac_steps: 0, a1_steps: 0 };

    let mut seq: RuleSequence = RuleSequence::default();
    let mut ac: Vec<AacState> = Vec::new();

    loop {
        if let Some(r) = a_sim.step_save_rule() {
            seq.push(r);
            ac.push(a_sim.state);
        }
        match a_sim.state {
            AacState::Halt(_) => break,
            AacState::A(1, _) => break,
            _ => (),
        }
    }
    (seq, ac)
}

fn write_array_1d_u64(out_fname: &str, data: Vec<u64>) -> io::Result<()> {
    let mut file = fs::File::create(out_fname)?;

    let mut writer = npyz::WriteOptions::new()
        .dtype(npyz::DType::Plain("<u8".parse::<TypeStr>().unwrap()))
        .writer(&mut file)
        .begin_1d()?;

    writer.extend(data)?;
    writer.finish()?;

    Ok(())
}

fn write_array_1d_u16(out_fname: &str, data: Vec<u16>) -> io::Result<()> {
    let mut file = fs::File::create(out_fname)?;

    let mut writer = npyz::WriteOptions::new()
        .dtype(npyz::DType::Plain("<u2".parse::<TypeStr>().unwrap()))
        .writer(&mut file)
        .begin_1d()?;

    writer.extend(data)?;
    writer.finish()?;

    Ok(())
}

fn save_fwd_sequence_c_vals() {
    let mut a_sim = AacSimulator::new();

    let mut c_vals = Vec::new();
    let mut ac_step_vals = Vec::new();

    println!("{:>13}", a_sim);
    for k in 1..=100000000 {
        a_sim.step();
        if let AacState::A(1, c) = a_sim.state {
            c_vals.push(c);
            ac_step_vals.push(a_sim.aac_steps);
            println!("{:>13}", a_sim);
        }
    }
    // wrong data type
    // write_array_1d_u64("c_vals_step_1e8.npy", c_vals).unwrap();
    // write_array_1d_u64("aac_step_vals_step_1e8.npy", ac_step_vals).unwrap();
}

fn save_integer_range_c_vals() {
    let mut delta_c_vals: Vec<u16> = Vec::new();
    let mut ac_step_vals: Vec<u16> = Vec::new();

    // println!("{:>13}", a_sim);
    for c in 1..=10000000 {
        let mut a_sim = AacSimulator { state: AacState::A(1, c), aac_steps: 0, a1_steps: 0 };
        // print!("{c} => ");
        loop {
            a_sim.step();
            if let AacState::A(1, c_next) = a_sim.state {
                // c_vals.push(c);
                // ac_step_vals.push(a_sim.aac_steps);
                // println!("delta c {}, {} steps", c_next - c, a_sim.aac_steps);
                delta_c_vals.push(u16::try_from(c_next - c).unwrap());
                ac_step_vals.push(u16::try_from(a_sim.aac_steps).unwrap());
                break;
            }
            if let AacState::Halt(n) = a_sim.state {
                // println!("halted with {n}, {} steps", a_sim.aac_steps);
                delta_c_vals.push(1);
                ac_step_vals.push(u16::try_from(a_sim.aac_steps).unwrap());
                break;
            }
        }
    }
    
    write_array_1d_u16("delta_c_c1-1e7.npy", delta_c_vals).unwrap();
    write_array_1d_u16("aac_step_vals_c1-1e7.npy", ac_step_vals).unwrap();
}

/// 2 * 3^n - 1, c_i odd, value of a after rules j^n
fn a_after_odd(n: u32) -> SNum {
    THREE.checked_pow(n).unwrap() * 2 - 1
}

/// 4 * 3^n - 1, c_i even, value of a after rules i j^n
fn a_after_even(n: u32) -> SNum {
    THREE.checked_pow(n).unwrap() * 4 - 1
}

/// 3^n - 2n, c_i odd, rules j^n
fn c_threshold_odd(n: u32) -> SNum {
    THREE.checked_pow(n).unwrap() - (n as SNum * 2)
}

/// 2 * 3^n - 2n - 4, c_i even, rules i j^n
fn c_threshold_even(n: u32) -> SNum {
    THREE.checked_pow(n).unwrap() * 2 - (n as SNum * 2) - 4
}

/// Use this struct to track what happens to (a, c) after a sequence of b, c, j rules.
/// 
/// Here, we let ce (c_excess) remain as a variable.
/// a = w * ce + x, 
/// c = y * ce + z. 
/// w, x, y, z are fractions
#[derive(Clone, Debug)]
struct FracCeState {
    w: Ratio<SNum>,
    x: Ratio<SNum>,
    y: Ratio<SNum>,
    z: Ratio<SNum>,
}

impl FracCeState {
    fn new_after_odd(n: u32) -> Self {
        FracCeState { w: Ratio::ZERO, x: Ratio::from_integer(a_after_odd(n)), y: Ratio::ONE, z: Ratio::ONE }
    }

    fn new_after_even(n: u32) -> Self {
        FracCeState { w: Ratio::ZERO, x: Ratio::from_integer(a_after_even(n)), y: Ratio::ONE, z: Ratio::ONE }
    }

    fn apply_rule(&self, rule: AacRule) -> Self {
        match rule {
            AacRule::B => FracCeState {
                w: self.w - self.y, 
                x: self.x - self.z - 2, 
                y: self.y * 3 / 2, 
                z: (self.z * 3 + 7) / 2
            },
            AacRule::C => FracCeState {
                w: self.w - self.y, 
                x: self.x - self.z - 4, 
                y: self.y * 3 / 2, 
                z: (self.z * 3 + 13) / 2
            },
            AacRule::J => FracCeState {
                w: self.w * 3, 
                x: self.x * 3 + 2, 
                y: self.y - self.w, 
                z: self.z - self.x + 1
            },
            AacRule::H => FracCeState {
                w: Ratio::ZERO, 
                x: Ratio::ONE, 
                y: self.w/2 + self.y, 
                z: self.x/2 + self.z + 2
            },
            _ => unimplemented!()
        }
    }

    fn threshold1(&self) -> Ratio<SNum> {
        assert!(self.w < self.y);
        (self.x - self.z) / (self.y - self.w)
    }

    fn threshold2(&self) -> Ratio<SNum> {
        assert!(self.w < self.y);
        (self.x - self.z - 4) / (self.y - self.w)
    }

    fn get_delta_c(&self, c_th: SNum) -> Option<SNum> {
        // state needs to be A(1, c) for integer c
        if !(self.w == Ratio::ZERO && self.x == Ratio::ONE && self.y == Ratio::ONE && self.z.is_integer()) {
            None
        } else {
            Some(self.z.numer() - c_th)
        }
    }
}

impl fmt::Display for FracCeState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "a = {}/{} c_e + {}/{}; ", self.w.numer(), self.w.denom(), self.x.numer(), self.x.denom())?;
        write!(f, "c = {}/{} c_e + {}/{}", self.y.numer(), self.y.denom(), self.z.numer(), self.z.denom())
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum CommonRule { BC, J, H }

#[derive(PartialEq, Eq, Clone, Copy)]
enum FractalRule {
    L, // branch left
    J, // branch right
    E  // end
}

impl FractalRule {
    fn num_halving(&self) -> u32 {
        match &self {
            FractalRule::L => 2,
            FractalRule::J => 0,
            FractalRule::E => 2,
        }
    }
}

fn fractal_to_common_rule_seq(v: &Vec<FractalRule>) -> Vec<CommonRule> {
    let mut out = Vec::new();
    for r in v {
        match r {
            FractalRule::L => out.extend_from_slice(&[CommonRule::BC, CommonRule::BC]),
            FractalRule::J => out.push(CommonRule::J),
            FractalRule::E => out.extend_from_slice(&[CommonRule::BC, CommonRule::H]),
        }
    }
    out
}

#[derive(Clone, Debug)]
struct ACModState {
    a: SNum,
    c: SNum,
    m: SNum, // mod, needs to be a power of 2
}

impl fmt::Display for ACModState {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "({}, {}) mod {}", self.a, self.c, self.m)
    }
}


#[derive(Clone, Debug)]
enum ACModError {
    ModTooSmall,
    BadRemainder,
}

impl ACModState {
    fn new_raw(a_after: SNum, c_excess: SNum, m: SNum) -> Self {
        assert!(c_excess % 2 == 0);

        Self {
            a: a_after % m,
            c: (c_excess + 1) % m,
            m
        }
    }

    fn new_after_odd(n: u32, c_excess: SNum, pow2: u32) -> Self {
        let a_after = a_after_odd(n);
        assert!(c_excess % 2 == 0);
        let m: SNum = TWO.checked_pow(pow2).unwrap();

        Self {
            a: a_after % m,
            c: (c_excess + 1) % m,
            m
        }
    }

    fn new_after_even(n: u32, c_excess: SNum, pow2: u32) -> Self {
        let a_after = a_after_even(n);
        assert!(c_excess % 2 == 0);
        let m: SNum = TWO.checked_pow(pow2).unwrap();

        Self {
            a: a_after % m,
            c: (c_excess + 1) % m,
            m
        }
    }

    fn try_apply_rule(&self, rule: CommonRule) -> Result<(ACModState, AacRule), ACModError> {
        use ACModError::*;
        match rule {
            CommonRule::BC => {
                if self.m < 4 {
                    Err(ModTooSmall)
                } else {
                    match self.c.rem_euclid(4) {
                        0 | 2 => Err(BadRemainder),
                        1 => {
                            let m_new = self.m / 2;
                            Ok((Self {
                                a: (self.a - self.c - 2).rem_euclid(m_new),
                                c: (3 * (self.c - 1)/2 + 5).rem_euclid(m_new),
                                m: m_new
                            }, AacRule::B))
                        },
                        3 => {
                            let m_new = self.m / 2;
                            Ok((Self {
                                a: (self.a - self.c - 4).rem_euclid(m_new),
                                c: (3 * (self.c - 1)/2 + 8).rem_euclid(m_new),
                                m: m_new
                            }, AacRule::C))
                        },
                        _ => unreachable!()
                    }
                }
            },
            CommonRule::H => {
                if self.m < 2 {
                    Err(ModTooSmall)
                } else if self.a.rem_euclid(2) != 0 || self.c.rem_euclid(2) != 1 {
                    Err(BadRemainder)
                } else {
                    let m_new = self.m/2;
                    Ok((Self {
                        a: ONE.rem_euclid(m_new),
                        c: (self.a/2 + self.c + 2).rem_euclid(m_new),
                        m: m_new
                    }, AacRule::H))
                }
            },
            CommonRule::J => {
                if self.m < 2 {
                    Err(ModTooSmall)
                } else if self.a.rem_euclid(2) != 1 || self.c.rem_euclid(2) != 1 {
                    Err(BadRemainder)
                } else {
                    Ok((Self {
                        a: (3 * self.a + 2).rem_euclid(self.m),
                        c: (self.c - self.a + 1).rem_euclid(self.m),
                        m: self.m
                    }, AacRule::J))
                }
            },
        }
    }

    fn try_rule_sequence(&self, rule_seq: &Vec<CommonRule>, verbose: bool) -> Result<(ACModState, Vec<AacRule>), ACModError> {
        let mut state = self.clone();
        if verbose {
            println!("{:?}", state);
        }

        let mut aac_rules = Vec::new();
        for r in rule_seq {
            match state.try_apply_rule(*r) {
                Ok((s_next, aac_rule)) => {
                    state = s_next.clone();
                    aac_rules.push(aac_rule);
                    if verbose {
                        println!("{} - {:?}", aac_rule, state);
                    }
                }
                Err(e) => {
                    if verbose {
                        println!("{:?}", e);
                    }
                    return Err(e);
                },
            }
        }
        Ok((state, aac_rules))
    }
}

#[derive(Clone, Copy, PartialEq)]
enum FractalType { Even, Odd }

impl FractalType {
    fn parity(&self) -> usize {
        match *self {
            FractalType::Even => 0,
            FractalType::Odd => 1,
        }
    }
}

#[derive(Clone)]
struct RunupInfo {
    n: u32,
    c_th: SNum,
    a_after: SNum,
    state_after: FracCeState,
    c_th_fn: fn(u32) -> SNum,
    a_after_fn: fn(u32) -> SNum,
    state_after_fn: fn(u32) -> FracCeState,
}

impl RunupInfo {
    fn new_odd(n: u32) -> Self {
        Self {
            n,
            c_th: c_threshold_odd(n),
            a_after: a_after_odd(n),
            state_after: FracCeState::new_after_odd(n),
            c_th_fn: c_threshold_odd,
            a_after_fn: a_after_odd,
            state_after_fn: FracCeState::new_after_odd,
        }
    }

    fn new_even(n: u32) -> Self {
        Self {
            n,
            c_th: c_threshold_even(n),
            a_after: a_after_even(n),
            state_after: FracCeState::new_after_even(n),
            c_th_fn: c_threshold_even,
            a_after_fn: a_after_even,
            state_after_fn: FracCeState::new_after_even,
        }
    }

    fn increment(&mut self) {
        self.n += 1;
        self.c_th = (self.c_th_fn)(self.n);
        self.a_after = (self.a_after_fn)(self.n);
        self.state_after = (self.state_after_fn)(self.n);
    }
}

#[derive(Clone)]
struct FractalWalker {
    info: RunupInfo,
    fractal_type: FractalType,
    location: FractalLocation,
}

impl FractalWalker {
    fn new_odd(n: u32) -> Self {
        Self {
            info: RunupInfo::new_odd(n),
            fractal_type: FractalType::Odd,
            location: FractalLocation::new_end(n, FractalType::Odd)
        }
    }

    fn new_even(n: u32) -> Self {
        Self {
            info: RunupInfo::new_even(n),
            fractal_type: FractalType::Even,
            location: FractalLocation::new_end(n, FractalType::Even)
        }
    }

    /// these bounds are approximate, but the behavior at the boundaries are edge cases 
    /// that I don't plan to accelerate anyway
    fn rough_tree_bounds(&self) -> (SNum, SNum) {
        let lower = self.info.c_th;
        let upper = match self.fractal_type {
            FractalType::Even => div_round_down(8 * THREE.pow(self.info.n) - 28, 5),
            FractalType::Odd  => div_round_down(4 * THREE.pow(self.info.n) - 28, 5),
        } + self.info.c_th - 1;
        (lower, upper)
    }

    fn new_tree(&self) -> CantorTreeWalker {
        let (root_c_min, root_c_max) = safe_tree_node_bounds(&self.info, &vec![TreeDirection::Left]);
        let root = NodeData::new(TreeDirection::Left, root_c_min, root_c_max);
        CantorTreeWalker { path: vec![root], bounds: self.rough_tree_bounds() }
    }

    fn next(&mut self) {
        let mut break_out_of_cantor_set: bool = false;

        match &mut self.location {
            FractalLocation::CantorSet(tree) => {
                loop {
                    let mut branch_direction: Option<TreeDirection> = None;
                    let curr_node = tree.path.last().unwrap();
                    if curr_node.can_branch_left {
                        branch_direction = Some(TreeDirection::Left);
                    } else if curr_node.can_visit {
                        tree.path.last_mut().unwrap().can_visit = false;

                        // we will be at this node now
                        break;
                    } else if curr_node.can_branch_right {
                        branch_direction = Some(TreeDirection::Right);
                    } else if tree.path.len() > 1 {
                        tree.path.pop();
                    } else {
                        // CantorSet -> End
                        break_out_of_cantor_set = true;
                        break;
                    }

                    if let Some(branch_direction) = branch_direction {
                        // mark that we have tried branching in this direction
                        let curr_node_mut = tree.path.last_mut().unwrap();
                        match branch_direction {
                            TreeDirection::Left => curr_node_mut.can_branch_left = false,
                            TreeDirection::Right => curr_node_mut.can_branch_right = false,
                        }

                        let mut d_vec: Vec<TreeDirection> = tree.path.iter().map(|n| n.direction).collect(); 
                        d_vec.push(branch_direction);

                        let (c_min, c_max) = safe_tree_node_bounds(&self.info, &d_vec);
                        if c_max >= c_min { // interval needs to have a positive length in order for acceleration to be possible
                            let delta_c_estimate = get_delta_c(c_min as Num).unwrap();

                            // two b or c rules per left branch of tree, also one b or c rule at the end
                            let num_halvings = d_vec.iter().filter(|d| **d == TreeDirection::Left).count() * 2 + 1;

                            let speedup = speedup_factor((c_max - c_min).try_into().unwrap(), 
                                num_halvings.try_into().unwrap(), delta_c_estimate);

                            if speedup >= 10 {
                                // then it is worth it to accelerate the node
                                tree.path.push(NodeData::new(branch_direction, c_min, c_max));
                            }
                        }
                    }
                }
            }
            FractalLocation::End { c_min: _, c_max: _ } => {
                self.info.increment();
                self.location = FractalLocation::CantorSet(self.new_tree());
                self.next();
            }
        }

        if break_out_of_cantor_set {
            self.location = FractalLocation::new_end(self.info.n, self.fractal_type);
        }
    }

    fn catch_up_to(&mut self, c_target: SNum) -> bool {
        let mut changed = false;
        while c_target > self.c_max() {
            self.next();
            changed = true;
        }
        changed
    }

    fn get_fractal_rules(&self) -> Vec<FractalRule> {
        let mut fractal_rules: Vec<FractalRule> = Vec::new();
        match &self.location {
            FractalLocation::CantorSet(tree) => {
                fractal_rules.extend(tree.path.iter().map(
                    |n| match n.direction {
                        TreeDirection::Left => FractalRule::L,
                        TreeDirection::Right => FractalRule::J,
                    }
                ));
            },
            FractalLocation::End { c_min: _, c_max: _ } => (),
        }
        fractal_rules.push(FractalRule::E);
        fractal_rules
    }

    fn cycle(&self, c0: SNum) -> Option<OneFractalCycleResult> {
        let fractal_rules = self.get_fractal_rules();

        let num_halvings: u32 = fractal_rules.iter().map(FractalRule::num_halving).sum();
        let common_rules = fractal_to_common_rule_seq(&fractal_rules);
        let modulo: SNum = TWO.checked_pow(num_halvings).unwrap();

        let c_excess = c0 - self.info.c_th;

        let mut c_excess_mod = c_excess % modulo;
        let mut delta_c_cumulative: SNum = 0;
        let mut cycle_info: HashMap<SNum, (SNum, SNum)> = HashMap::new();
        let mut step_idx = 0;
        cycle_info.insert(c_excess_mod, (step_idx, delta_c_cumulative));

        loop {
            step_idx += 1;
            let mod_state = ACModState::new_raw(self.info.a_after, c_excess_mod, modulo);
            let (_, aac_rules) = mod_state.try_rule_sequence(&common_rules, false).unwrap();
            let mut frac_state = self.info.state_after.clone();
            for r in aac_rules {
                frac_state = frac_state.apply_rule(r);
            }
            let delta_c = frac_state.get_delta_c(self.info.c_th).unwrap();
            if delta_c % 2 != 0 {
                return None;
            }

            c_excess_mod = (c_excess_mod + delta_c) % modulo;
            delta_c_cumulative += delta_c;

            if let Some((step_preperiod, delta_c_preperiod)) = cycle_info.get(&c_excess_mod) {
                let step_period = step_idx - step_preperiod;
                let delta_c_period = delta_c_cumulative - delta_c_preperiod;

                let c_preperiod = c0 + delta_c_preperiod;
                let n_periods = (self.c_max() - c_preperiod) / delta_c_period;
                let c_final = c_preperiod + n_periods * delta_c_period;
                let n_a1_steps = step_preperiod + n_periods * step_period;
                let n_aac_per_a1 = common_rules.len() as SNum + self.info.n as SNum 
                    + if self.fractal_type == FractalType::Even {1} else {0}; // even c0 => extra i rule
                let n_aac_steps = n_a1_steps * n_aac_per_a1;

                return Some(OneFractalCycleResult { c_final, n_a1_steps, n_aac_steps,
                    step_period, step_preperiod: *step_preperiod
                });
            } else {
                cycle_info.insert(c_excess_mod, (step_idx, delta_c_cumulative));
            }
        }

    }

    fn c_min(&self) -> SNum {
        match &self.location {
            FractalLocation::CantorSet(tree) => {
                match tree.path.last() {
                    Some(n) => n.c_min,
                    None => tree.bounds.0,
                }
            }
            FractalLocation::End { c_min, c_max: _ } => {
                *c_min
            }
        }
    }

    fn c_max(&self) -> SNum {
        match &self.location {
            FractalLocation::CantorSet(tree) => {
                match tree.path.last() {
                    Some(n) => n.c_max,
                    None => tree.bounds.1,
                }
            }
            FractalLocation::End { c_min: _, c_max } => {
                *c_max
            }
        }
    }

    fn depth(&self) -> usize {
        match &self.location {
            FractalLocation::CantorSet(w) => {
                w.path.len()
            },
            FractalLocation::End { c_min: _, c_max: _ } => 1,
        }
    }
}

#[derive(Debug)]
struct OneFractalCycleResult {
    c_final: SNum,
    n_a1_steps: SNum,
    n_aac_steps: SNum,
    step_period: SNum,
    step_preperiod: SNum,
}

#[derive(Debug)]
struct FractalCycle {
    c_final: SNum,
    n_a1_steps: SNum,
    n_aac_steps: SNum,
    step_period: [SNum; 2],
    step_preperiod: [SNum; 2],
    limiting_parity: usize,
}

#[derive(Debug)]
enum TwoFractalCycleResult {
    Cycle(FractalCycle),
    ShortIntervalError { limiting_parity: usize },
}

/// I have a sketch of a proof (not complete) showing that for sequences of steps with rules b, c, j, h,
/// where you must fix the j and h rules but can choose between rules b or c, you only need
/// to consider the cases where it's all b or all c when considering the bounds for the c values
/// that follow this kind of sequence.
fn safe_tree_node_bounds(info: &RunupInfo, directions: &Vec<TreeDirection>) -> (SNum, SNum) {
    let state2_b = {
        let mut state = info.state_after.clone();
        for d in directions {
            match d {
                TreeDirection::Left => {
                    state = state.apply_rule(AacRule::B);
                    state = state.apply_rule(AacRule::B);
                },
                TreeDirection::Right => {
                    state = state.apply_rule(AacRule::J);
                }
            }
        }
        state
    };

    let state2_c = {
        let mut state = info.state_after.clone();
        for d in directions {
            match d {
                TreeDirection::Left => {
                    state = state.apply_rule(AacRule::C);
                    state = state.apply_rule(AacRule::C);
                },
                TreeDirection::Right => {
                    state = state.apply_rule(AacRule::J);
                }
            }
        }
        state
    };

    let threshold2b = eval_round_down_to_even_integer(state2_b.threshold2());
    let threshold2c = eval_round_down_to_even_integer(state2_c.threshold2());

    let state1_b = state2_b.apply_rule(AacRule::B);
    let state1_c = state2_c.apply_rule(AacRule::C);
    let threshold1b = eval_round_up_to_even_integer(state1_b.threshold1());
    let threshold1c = eval_round_up_to_even_integer(state1_c.threshold1());

    // println!("1b {} 1c {}; 2b {} 2c {}", 
    //     info.c_th + threshold1b, info.c_th + threshold1c, 
    //     info.c_th + threshold2b, info.c_th + threshold2c);

    let c_min = info.c_th + threshold1b.max(threshold1c);
    let c_max = info.c_th + threshold2b.min(threshold2c);
    
    (c_min, c_max)
}

fn eval_round_down_to_even_integer(r: Ratio<SNum>) -> SNum {
    div_round_down_to_even_integer(*r.numer(), *r.denom())
}

fn eval_round_up_to_even_integer(r: Ratio<SNum>) -> SNum {
    div_round_up_to_even_integer(*r.numer(), *r.denom())
}

fn div_round_up_to_even_integer(a: SNum, b: SNum) -> SNum {
    let mut res = a/b;
    let rem = a % b;
    if rem != 0 && res >= 0 {
        res += 1;
    }
    if res % 2 != 0 {
        res += 1;
    }
    res
}

fn div_round_down_to_even_integer(a: SNum, b: SNum) -> SNum {
    let mut res = a/b;
    let rem = a % b;
    if rem != 0 && res < 0 {
        res -= 1;
    }
    if res % 2 != 0 {
        res -= 1;
    }
    res
}

fn div_round_down(a: SNum, b: SNum) -> SNum {
    let mut res = a/b;
    let rem = a % b;
    if rem != 0 && res < 0 {
        res -= 1;
    }
    res
}

#[derive(Clone)]
enum FractalLocation {
    CantorSet(CantorTreeWalker),
    End {
        c_min: SNum,
        c_max: SNum,
    }
}

impl FractalLocation {
    fn safe_end_fractal_bounds_odd(n: u32) -> (SNum, SNum) {
        let c_max = c_threshold_odd(n+1) - 4;
        let c_min = c_threshold_odd(n) + div_round_up_to_even_integer(4 * THREE.pow(n) - 18, 5);
        (c_min, c_max)
    }

    fn safe_end_fractal_bounds_even(n: u32) -> (SNum, SNum) {
        let c_max = c_threshold_even(n+1) - 4;
        let c_min = c_threshold_even(n) + div_round_up_to_even_integer(8 * THREE.pow(n) - 18, 5);
        (c_min, c_max)
    }

    fn new_end(n: u32, f_type: FractalType) -> Self {
        let (c_min, c_max) = match f_type {
            FractalType::Even => FractalLocation::safe_end_fractal_bounds_even(n),
            FractalType::Odd => FractalLocation::safe_end_fractal_bounds_odd(n),
        };
        Self::End { c_min, c_max }
    }

    /// not sure if needed
    fn c_min(&self) -> SNum {
        match self {
            FractalLocation::CantorSet(w) => {
                todo!()
            },
            FractalLocation::End { c_min, c_max: _ } => *c_min,
        }
    }

    /// not sure if needed
    fn c_max(&self) -> SNum {
        match self {
            FractalLocation::CantorSet(w) => {
                todo!()
            },
            FractalLocation::End { c_min: _, c_max } => *c_max,
        }
    }
}

impl fmt::Display for FractalWalker {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} {} ", match self.fractal_type {
            FractalType::Even => "Even",
            FractalType::Odd => "Odd",
        }, self.info.n)?;

        match &self.location {
            FractalLocation::CantorSet(tree) => {
                if tree.path.is_empty() {
                    write!(f, "(no tree) {} {}", tree.bounds.0, tree.bounds.1)?;
                } else {
                    for node in &tree.path {
                        write!(f, "{}", match node.direction {
                            TreeDirection::Left => "L",
                            TreeDirection::Right => "R",
                        })?;
                    }
                    let curr_node = tree.path.last().unwrap();
                    write!(f, " {} {}", curr_node.c_min, curr_node.c_max)?;
                }
            }
            FractalLocation::End { c_min, c_max } => {
                write!(f, "End {c_min} {c_max}")?;
            }
        }
        Ok(())
    }
}

#[derive(Clone)]
struct CantorTreeWalker {
    path: Vec<NodeData>,
    bounds: (SNum, SNum)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum TreeDirection {
    Left,
    Right
}

#[derive(Clone)]
struct NodeData {
    direction: TreeDirection,
    can_branch_left: bool,
    can_visit: bool,
    can_branch_right: bool,
    c_min: SNum,
    c_max: SNum,
}

impl NodeData {
    fn new(direction: TreeDirection, c_min: SNum, c_max: SNum) -> Self {
        Self {
            direction,
            can_branch_left: true,
            can_visit: true,
            can_branch_right: true,
            c_min, c_max
        }
    }
}

#[derive(Debug)]
enum CycleSimState {
    A1 { c: Num },
    Halt(Num)
}

impl fmt::Display for CycleSimState {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            CycleSimState::A1 { c } => write!(f, "A(1, {})", c),
            CycleSimState::Halt(n) => write!(f, "Halt({})", n),
        }
    }
}

struct CycleSimulator {
    state: CycleSimState,
    aac_steps: Num,
    a1_steps: Num,
    self_steps: Num,
    f_walkers: [FractalWalker; 2],
}

impl fmt::Display for CycleSimulator {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} | ", self.self_steps)?;
        write!(f, "{} | {}:  ", self.a1_steps, self.aac_steps)?;
        write!(f, "{}; {}, {}", self.state, self.f_walkers[0], self.f_walkers[1])
    }
}

impl CycleSimulator {
    fn new() -> Self {
        let mut w_e = FractalWalker::new_even(6);
        let mut w_o = FractalWalker::new_odd(6);

        w_e.catch_up_to(w_o.c_min());
        w_o.catch_up_to(w_e.c_min());

        Self {
            state: CycleSimState::A1{ c: 3 },
            aac_steps: 1,
            a1_steps: 1,
            self_steps: 0,
            f_walkers: [w_e, w_o],
        }
    }

    fn walkers_catch_up_to(&mut self, c: SNum) {
        for w in self.f_walkers.iter_mut() {
            w.catch_up_to(c);
        }
    }

    fn basic_step(&mut self) -> Option<RuleSequence> {
        if let CycleSimState::A1{ mut c } = self.state {
            let mut a: Num = 1;
            let mut seq = RuleSequence(Vec::new());
            let mut halt_val: Option<Num> = None;
            
            loop {
                use AacRule::*;
                self.aac_steps += 1;
                let rule = if c % 2 == 0 {
                    if c >= a {
                        if a % 2 == 0 {
                            halt_val = Some(a/2 + c + 4);
                            G
                        } else {
                            c = c - a + 4;
                            a *= 3;
                            I
                        }
                    } else {
                        a = a - c - 1;
                        c = 3*c/2 + 2;
                        A
                    }
                } else {
                    if c >= a {
                        if a % 2 == 0 {
                            c = a/2 + c + 2;
                            a = 1;
                            H
                        } else {
                            c = c - a + 1;
                            a = 3*a + 2;
                            J
                        }
                    } else if c + 1 == a {
                        halt_val = Some(3 * (c-1) / 2 + 4);
                        F   
                    } else { // c <= a - 2
                        if c % 4 == 1 {
                            a = a - c - 2;
                            c = 3 * (c - 1)/2 + 5;
                            B
                        } else { // c == 3 (mod 4)
                            if c + 2 == a {
                                a = 3*c + 8;
                                c = 1;
                                E
                            } else if c + 3 == a {
                                halt_val = Some(3 * (c-1) / 2 + 7);
                                D
                            } else { // c <= a - 4
                                a = a - c - 4;
                                c = 3*(c - 1)/2 + 8;
                                C
                            }
                        }
                    }
                };
                seq.push(rule);

                if let Some(n) = halt_val {
                    self.state = CycleSimState::Halt(n);
                    return Some(seq);
                }

                if a == 1 {
                    self.a1_steps += 1;
                    self.state = CycleSimState::A1 { c };
                    return Some(seq);
                }
            }
        } else {
            return None;
        }
    }

    fn big_step(&mut self) -> bool {
        self.self_steps += 1;
        if let CycleSimState::A1 { c } = self.state {
            let c_goal: Num = self.f_walkers[0].c_min().max(self.f_walkers[1].c_min()).try_into().unwrap();
            if c < c_goal {
                // println!("basic steps until {c_goal}");
                let halted = self.basic_steps_until(c_goal);
                return halted;
            } else {
                // println!("cycle");
                self.cycle();
                return false;
            }
        } else {
            return true;
        }
    }

    /// returns whether the TM has halted or not
    fn basic_steps_until(&mut self, c_goal: Num) -> bool {
        loop {
            match self.state {
                CycleSimState::A1 { c } => {
                    if c < c_goal {
                        self.basic_step();
                    } else {
                        return false;
                    }
                }
                CycleSimState::Halt(n) => {
                    println!("Halt({n})");
                    return true;
                }
            }
        }
    }

    /// At the end of this function, the two FractalWalkers must have overlapping intervals,
    /// and they must not be behind the c of A(1,c).
    fn cycle(&mut self) {
        let CycleSimState::A1 {c: c0} = self.state else {
            unreachable!()
        };
        let c0: SNum = c0.try_into().unwrap();

        assert!(c0 >= self.f_walkers[0].c_min());
        assert!(c0 >= self.f_walkers[1].c_min());
        // if c0 > self.f_walkers[0].c_max() {
        //     eprintln!("oh no, c0 > c_max_0, {} {}", c0, self.f_walkers[0].c_max());
        // }
        assert!(c0 <= self.f_walkers[0].c_max());
        assert!(c0 <= self.f_walkers[1].c_max());

        if !self.one_walker_cycle(c0) {
            self.two_walker_cycle(c0);
        }
        loop {
            if !self.f_walkers[0].catch_up_to(self.f_walkers[1].c_min()) &&
                !self.f_walkers[1].catch_up_to(self.f_walkers[0].c_min()) {
                    break;
                }
        }
    }

    fn one_walker_cycle(&mut self, c0: SNum) -> bool {
        let parity: usize = (c0 % 2).try_into().unwrap();

        if let Some(res) = self.f_walkers[parity].cycle(c0) {
            self.a1_steps += Num::try_from(res.n_a1_steps).unwrap();
            self.aac_steps += Num::try_from(res.n_aac_steps).unwrap();
            self.state = CycleSimState::A1 { c: Num::try_from(res.c_final).unwrap() };
            self.f_walkers[parity].next();
            self.f_walkers[1 - parity].catch_up_to(
                res.c_final.max(self.f_walkers[parity].c_min()));
            true
        } else {
            false
        }
    }

    fn two_walker_cycle(&mut self, c0: SNum) {
        match self.solve_two_walker_cycle(c0) {
            TwoFractalCycleResult::Cycle(res) => {
                self.a1_steps += Num::try_from(res.n_a1_steps).unwrap();
                self.aac_steps += Num::try_from(res.n_aac_steps).unwrap();
                self.state = CycleSimState::A1 { c: Num::try_from(res.c_final).unwrap() };
                self.f_walkers[res.limiting_parity].next();
                self.f_walkers[1 - res.limiting_parity].catch_up_to(
            res.c_final.max(self.f_walkers[res.limiting_parity].c_min()));
            }
            TwoFractalCycleResult::ShortIntervalError { limiting_parity } => {
                self.f_walkers[limiting_parity].next();
                self.f_walkers[1 - limiting_parity].catch_up_to(self.f_walkers[limiting_parity].c_min());
            }
        }
    }

    fn solve_two_walker_cycle(&self, c0: SNum) -> TwoFractalCycleResult {
        let fractal_rules = [self.f_walkers[0].get_fractal_rules(),
            self.f_walkers[1].get_fractal_rules()];
        let nh0: u32 = fractal_rules[0].iter().map(FractalRule::num_halving).sum();
        let nh1: u32 = fractal_rules[1].iter().map(FractalRule::num_halving).sum();
        let num_halvings = nh0.max(nh1);
        let modulo: SNum = TWO.checked_pow(num_halvings).unwrap();
        let common_rules = [fractal_to_common_rule_seq(&fractal_rules[0]),
            fractal_to_common_rule_seq(&fractal_rules[1])];

        // println!("num_halvings {num_halvings}");

        let mut c_mod = c0 % modulo;
        let mut delta_c_cumulative: SNum = 0;
        let mut n_steps: [SNum; 2] = [0, 0];
        let mut cycle_info: HashMap<SNum, ([SNum; 2], SNum)> = HashMap::new();
        cycle_info.insert(c_mod, (n_steps, delta_c_cumulative));

        loop {
            let parity: usize = (c_mod % 2).try_into().unwrap();
            n_steps[parity] += 1;
            let p_info = &self.f_walkers[parity].info;
            let c_excess_mod = (c_mod - p_info.c_th).rem_euclid(modulo);
            let mod_state = ACModState::new_raw(p_info.a_after, c_excess_mod, modulo);
            let (_, aac_rules) = mod_state.try_rule_sequence(&common_rules[parity], false).unwrap();

            // {
            //     let mut seq: RuleSequence = RuleSequence::default();
            //     for r in &aac_rules {
            //         seq.push(*r);
            //     }
            //     print!("{c_mod}_{c_excess_mod}_{parity}_{seq} ");
            // }

            let mut frac_state = p_info.state_after.clone();
            for r in aac_rules {
                frac_state = frac_state.apply_rule(r);
            }
            let delta_c = frac_state.get_delta_c(p_info.c_th).unwrap();

            c_mod = (c_mod + delta_c) % modulo;
            delta_c_cumulative += delta_c;

            if let Some((step_preperiod, delta_c_preperiod)) = cycle_info.get(&c_mod) {
                let step_period = [n_steps[0] - step_preperiod[0], 
                    n_steps[1] - step_preperiod[1]];
                let delta_c_period = delta_c_cumulative - delta_c_preperiod;

                let c_preperiod = c0 + delta_c_preperiod;
                let c_maxes = [self.f_walkers[0].c_max(), self.f_walkers[1].c_max()];
                for limiting_parity in 0..2 {
                    if c_preperiod >= c_maxes[limiting_parity] && step_preperiod[limiting_parity] > 0 {
                        eprintln!("Warning: interval too short, preperiod {c_preperiod}, limit in fractal {}", &self.f_walkers[limiting_parity]);
                        return TwoFractalCycleResult::ShortIntervalError { limiting_parity };
                    }
                }
                assert!(step_period[0] > 0 || step_period[1] > 0);
                let limiting_parity = if step_period[0] == 0 {
                    1
                } else if step_period[1] == 0 {
                    0
                } else if c_maxes[0] < c_maxes[1] {
                    0
                } else {
                    1
                };
                let c_max = c_maxes[limiting_parity];
                let n_periods = (c_max - c_preperiod) / delta_c_period;
                let c_final = c_preperiod + n_periods * delta_c_period;
                let n_a1_steps = (step_preperiod[0] + n_periods * step_period[0],
                    step_preperiod[1] + n_periods * step_period[1]);
                let n_aac_per_a1 = (common_rules[0].len() as SNum + self.f_walkers[0].info.n as SNum + 1, // extra i rule for even
                    common_rules[1].len() as SNum + self.f_walkers[1].info.n as SNum);
                let n_aac_steps = (n_a1_steps.0 * n_aac_per_a1.0,
                    n_a1_steps.1 * n_aac_per_a1.1);
                return TwoFractalCycleResult::Cycle(FractalCycle {
                    c_final,
                    n_a1_steps: n_a1_steps.0 + n_a1_steps.1,
                    n_aac_steps: n_aac_steps.0 + n_aac_steps.1,
                    step_period,
                    step_preperiod: *step_preperiod,
                    limiting_parity,
                });
            } else {
                cycle_info.insert(c_mod, (n_steps, delta_c_cumulative));
            }
        }
    }
}

fn speedup_factor(c_range: Num, num_halvings: u32, delta_c_estimate: Num) -> Num {
    let accelerated_cost: Num = 2u128.pow(num_halvings) * delta_c_estimate;
    c_range / accelerated_cost
}

fn main() {
    let tm = TuringMachine::from_standard_notation("1RB2LC1RC_2LC---2RB_2LA0LB0RA");

    // 10A>, 1<E01

    let rules_guess = "";

// 10A> 011 -> *HALT*

    // check_text_config_transition_rules(&tm, rules_guess);

    let always = |_: &BasicSimulator| true;
    let highlight = |sim: &BasicSimulator| {
        (sim.state == State::D && sim.prev_dir == Some(TMDirection::Right)) ||
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position+1) == Some(&Symbol(1)))
    };
    let highlight2 = |sim: &BasicSimulator| {
        (sim.state == State::C && sim.prev_dir == Some(TMDirection::Right) && sim.tape.get(sim.position) == Some(&Symbol(1))) ||
        (sim.state == State::B && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position+1) == Some(&Symbol(1)))
    };
    let basic_state = |sim: &BasicSimulator| {
        sim.tape.get(0) == Some(&Symbol(1)) && sim.prev_dir == Some(TMDirection::Left)
        && (sim.position == 0 || (1..=sim.position).into_iter().all(|i| sim.tape.get(i) == Some(&Symbol(2))))
    };

    // for c in (150..272).step_by(2) {
    // for c in (272..=470).step_by(2) {
    // for c in (150..=470).step_by(2) {
    // for c in (148..=472).step_by(2) {
    // for c in (472..=1442).step_by(2) {
    // let st = 70001;
    // for c in (st..=st+1000).step_by(2) {
    // for c in (233..=717).step_by(2) {
    // let (c_th1, c_th2) = FractalLocation::safe_end_fractal_bounds_even(6);
    let (c_th1, c_th2) = {
        use TreeDirection::Left as L;
        use TreeDirection::Right as R;
        safe_tree_node_bounds(&RunupInfo::new_odd(10), &vec![L, L, R, R, L, R])
    };

    for c in ((c_th1-8)..=(c_th2+8)).step_by(2) {
        // println!("{} {}", c, get_rule_sequence(c));
        if c == c_th1 || c == c_th2 {
            println!("c bound = {}", c);
        }

        let (seq, states) = get_rule_ac_sequence(c.try_into().unwrap());
        print!("{} {} ", c, seq);
        for state in states {
            match state {
                AacState::A(curr_a, curr_c) => print!("{curr_a},{curr_c} "),
                AacState::Halt(n) => print!("Halt({n})"),
            }

            // if let AacState::A(1, c_next) = state {
            //     print!(" delta_c is {} {:?}", c_next as i64 - c, get_delta_c(c.try_into().unwrap()));
            // }
        }
        println!();
    }
    println!();


    // let mut walker = FractalWalker::new_odd(3);
    // for k in 0..100 {
    //     println!("{}", walker);
    //     walker.next();
    // }

    let mut w_e = FractalWalker::new_even(6);
    let mut w_o = FractalWalker::new_odd(6);
    println!("{w_e}\n{w_o}");

    w_o.catch_up_to(w_e.c_min());
    w_e.catch_up_to(w_o.c_min());

    println!("{w_e}\n{w_o}");


    // let c0 = 16410;
    // let c0 = 8191;

    check_fractal_positions(1802000);
    
    // try_one_fractal_cycle(8155);
    // try_two_fractal_cycle(1823124, 1823144);

    let mut cycle_sim = CycleSimulator::new();
    println!("{cycle_sim}");
    for k in 0..1000000 {
        let halted = cycle_sim.big_step();
        if cycle_sim.f_walkers[0].depth() < 4 && cycle_sim.f_walkers[1].depth() < 4 {
            println!("{cycle_sim}");
        }
        if halted {
            break;
        }
    }
    // let n_steps = 3000;
    // let mut cycle_sim = CycleSimulator::new();
    // let mut aac_sim = AacSimulator::new();

    // println!("{cycle_sim}");
    // for k in 0..n_steps {
    //     println!("{k}");
    //     while aac_sim.aac_steps < cycle_sim.aac_steps {
    //         aac_sim.step();
    //     }
    //     println!("{cycle_sim}");
    //     println!("{aac_sim}");
    //     let halted = cycle_sim.big_step();
    //     if halted {
    //         break;
    //     }
    // }

    // println!("{}", get_rule_sequence(223));

    // run_basic_sim(&tm, 5000, basic_state);
    // run_basic_sim(&tm, 1000, always);

    // let mut a_sim = AacSimulator::new();
    // let mut a_sim = AacSimulator {
    //     aac_steps: 100000000000,
    //     a1_steps:  3463811024,
    //     state: AacState::A(258280325, 229003647303)
    // };

    
    // println!("{:?}", c_vals);

    // for k in 1..=100 {
    // for k in 1..=100000000000u64 {
        // a_sim.step();
    //     if k % 1000000000 == 0 {
            // println!("{:>13}", a_sim);
    //     }
        // if matches!(a_sim.state, AacState::A(1, _)) {
        //     println!("{:>10}", a_sim);
        // }
    // }
    // println!("{:>13}", a_sim);


    // let mut sim = BasicSimulator::new(tm);
    // println!("{}", sim.display_directed_head());
    // for _ in 0..2000 {
    //     let BasicStepInfo { halted: _, record} = sim.step();
    //     println!("{}", sim.display_directed_head());
    // }

    // investigate_bc_sequences();

}

fn check_fractal_positions(c: SNum) {
    let mut walker0 = FractalWalker::new_even(3);
    let mut walker1 = FractalWalker::new_odd(3);
    walker0.catch_up_to(c);
    walker1.catch_up_to(c);
    println!("c {c}\n{walker0} {:?}\n{walker1} {:?}", walker0.rough_tree_bounds(), walker1.rough_tree_bounds());
}

fn try_two_fractal_cycle(c0_low: SNum, c0_high: SNum, ) {
    let mut cycle_sim = CycleSimulator::new();
    cycle_sim.walkers_catch_up_to(c0_low);

    for c0 in c0_low..c0_high {
        let res = cycle_sim.solve_two_walker_cycle(c0);
        println!("c_initial {c0} -> {:?}", res);

        if let TwoFractalCycleResult::Cycle(cyc) = res {
            let mut c = c0;
            let mut n_a1_steps = 0;
            // let mut print_count = 0;
            let mut matched = false;
            while c <= cyc.c_final {
                if c == cyc.c_final {
                    // println!("c matched {c} after {n_a1_steps} A1 steps");
                    if n_a1_steps == cyc.n_a1_steps {
                        // println!("A1 step number matches");
                        matched = true;
                        break;
                    }
                }

                let (seq, states) = get_rule_ac_sequence(c.try_into().unwrap());
                // print!("{} {} ", c, seq);
                // print_count += 1;
                // if print_count % ((res.step_period[0] + res.step_period[1])) == 0 {
                //     println!();
                // }

                if let Some(AacState::A(1, c_next)) = states.last() {
                    c = (*c_next).try_into().unwrap();
                } else {
                    break;
                }
                n_a1_steps += 1;
            }
            if !matched {
                eprintln!("c_final or number of A1 steps did not match prediction");
            }
            // println!();
            // println!();
        }
    }
}

fn try_one_fractal_cycle(c00: SNum) {
    let mut walker0 = FractalWalker::new_odd(3);
    walker0.catch_up_to(c00);
    println!("caught up to {walker0}");

    for c0 in (walker0.c_min()..=(walker0.c_min() + 32)).step_by(2) {
        let res = walker0.cycle(c0);
        println!("c_initial {c0} -> {:?}", &res);

        if let Some(res) = res {
            let mut c = c0;
            while c <= res.c_final {
                let (seq, states) = get_rule_ac_sequence(c.try_into().unwrap());
                print!("{} {} ", c, seq);
                if let Some(AacState::A(1, c_next)) = states.last() {
                    c = (*c_next).try_into().unwrap();
                } else {
                    break;
                }
            }
            println!();
        }
        println!();
    }
}

fn investigate_bc_sequences() {
    let state_j5 = FracCeState::new_after_odd(5);
    let c_th_j5 = c_threshold_odd(5);

    println!("{state_j5}");
    let rule_seqs = {
        use AacRule::*;
        // vec![
        //     vec![B, B, J, B, B, B],
        //     vec![C, C, J, C, C, C],
        //     vec![B, B, J, B, B],
        //     vec![C, C, J, C, C]
        // ]
        // vec![
        //     vec![B, B, B],
        //     vec![C, C, C],
        //     vec![B, B],
        //     vec![C, C]
        // ]
        vec![
            vec![B, B, J, B],
            vec![C, C, J, C],
            vec![B, B, J],
            vec![C, C, J]
        ]
    };

    for (i, rule_seq) in rule_seqs.iter().enumerate() {
        let mut state = state_j5.clone();
        for rule in rule_seq {
            state = state.apply_rule(*rule);
        }
        let threshold = if i < 2 {
            state.threshold1()
        } else {
            state.threshold2()
        };
        let threshold_f = c_th_j5 as f64 + *threshold.numer() as f64 / *threshold.denom() as f64;
        println!("{state}, {threshold_f}");
        if i >= 5 {
            println!(" -(bh)-> delta c {:?}", state.apply_rule(AacRule::B).apply_rule(AacRule::H).get_delta_c(c_th_j5));
            println!(" -(ch)-> delta c {:?}", state.apply_rule(AacRule::C).apply_rule(AacRule::H).get_delta_c(c_th_j5));
        }
    }

    let fractal_rule_seq = {
        use FractalRule::*;
        vec![L, J, L, E]
    };
    let num_halvings: u32 = fractal_rule_seq.iter().map(FractalRule::num_halving).sum();
    let rules2 = fractal_to_common_rule_seq(&fractal_rule_seq);

    let mstate = ACModState::new_after_odd(11, 4, num_halvings);
    if let Ok((_, rules)) = mstate.try_rule_sequence(&rules2, true) {
        for r in rules {
            print!("{}", r);
        }
        println!();
    }

    let my_n = 7;
    let state_jn = FracCeState::new_after_odd(my_n);
    let c_th_jn = c_threshold_odd(my_n);

    for c_e in (0..2i128.pow(num_halvings)).step_by(2) {
        let (_, rules) = ACModState::new_after_odd(my_n, c_e, num_halvings).try_rule_sequence(&rules2, false).unwrap();
        print!("{c_e}: ");
        for r in &rules {
            print!("{}", r);
        }

        let mut state_from_ce = state_jn.clone();
        for r in rules {
            state_from_ce = state_from_ce.apply_rule(r);
        }
        print!(" delta c {:?}", state_from_ce.get_delta_c(c_th_jn));

        println!();
    }
}

fn investigate_parities() {
    let mut sim = CycleSimulator::new();

    let mut max_streak_len = 0;

    let mut streak_len = 0;
    let mut streak_parity = 0;
    let mut streak_start = 0;

    println!("len   start     end before");

    for k in 0..10000 {
        sim.basic_step();

        match sim.state {
            CycleSimState::A1 { c } => {
                // println!("{}", c);
                let curr_parity = c % 2;
                if curr_parity == streak_parity {
                    streak_len += 1;
                } else {
                    if streak_len > max_streak_len {
                        max_streak_len = streak_len;
                        println!("{max_streak_len}, {streak_start}, {c}");
                    }

                    streak_len = 1;
                    streak_start = c;
                    streak_parity = curr_parity;
                }
            }
            CycleSimState::Halt(_) => break,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_div_round() {
        assert_eq!(div_round_up_to_even_integer(32, 8), 4);
        assert_eq!(div_round_up_to_even_integer(32, 7), 6);
        assert_eq!(div_round_up_to_even_integer(32, -7), -4);
        assert_eq!(div_round_up_to_even_integer(33, 8), 6);
        assert_eq!(div_round_up_to_even_integer(28, 7), 4);
        assert_eq!(div_round_up_to_even_integer(2, 3), 2);
        assert_eq!(div_round_up_to_even_integer(0, 3), 0);
        assert_eq!(div_round_up_to_even_integer(0, -1), 0);
    }

    #[test]
    fn test_fractal_end_bounds() {
        for n in 2..=7 {
            let (c_th1, c_th2) = FractalLocation::safe_end_fractal_bounds_even(n);
            for c in (c_th1..=c_th2).step_by(2) {
                let (seq, _) = get_rule_ac_sequence(c.try_into().unwrap());
                assert_eq!(seq.0.len(), 4);
                assert_eq!(seq.0[0], (AacRule::I, 1));
                assert_eq!(seq.0[1], (AacRule::J, n));
                assert!(matches!(seq.0[2], (AacRule::B | AacRule::C, 1)));
                assert_eq!(seq.0[3], (AacRule::H, 1));
            }

            let (c_th1, c_th2) = FractalLocation::safe_end_fractal_bounds_odd(n);
            for c in (c_th1..=c_th2).step_by(2) {
                let (seq, _) = get_rule_ac_sequence(c.try_into().unwrap());
                assert_eq!(seq.0.len(), 3);
                assert_eq!(seq.0[0], (AacRule::J, n));
                assert!(matches!(seq.0[1], (AacRule::B | AacRule::C, 1)));
                assert_eq!(seq.0[2], (AacRule::H, 1));
            }
        }
    }
}