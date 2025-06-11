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

type Num = u64;
type SNum = i64;
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
    aac_steps: u64,
    a1_steps: u64,
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

fn get_rule_sequence(c0: u64) -> RuleSequence {
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

fn get_rule_ac_sequence(c0: u64) -> (RuleSequence, Vec<AacState>) {
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
    write_array_1d_u64("c_vals_step_1e8.npy", c_vals).unwrap();
    write_array_1d_u64("aac_step_vals_step_1e8.npy", ac_step_vals).unwrap();
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

enum FractalType { Even, Odd }

impl FractalType {
    fn parity(&self) -> usize {
        match *self {
            FractalType::Even => 0,
            FractalType::Odd => 1,
        }
    }
}

struct FractalWalker {
    n: u32,
    c_th: SNum,
    a_after: SNum,
    c_th_fn: fn(u32) -> SNum,
    a_after_fn: fn(u32) -> SNum,
    fractal_type: FractalType,
    // location: FractalLocation,
}

impl FractalWalker {
    fn new_odd(n: u32) -> Self {
        Self {
            n,
            c_th: c_threshold_odd(n),
            a_after: a_after_odd(n),
            c_th_fn: c_threshold_odd,
            a_after_fn: a_after_odd,
            fractal_type: FractalType::Odd,
            // location: 
        }
    }

    fn new_even(n: u32) -> Self {
        todo!()
    }
}

enum FractalLocation {
    CantorSet(CantorTreeWalker),
    End {
        c_min: SNum,
        c_max: SNum,
    }
}

struct CantorTreeWalker {
    path: Vec<NodeData>
}

enum TreeDirection {
    Left,
    Right
}

struct NodeData {
    direction: TreeDirection,
    can_branch_left: bool,
    can_branch_right: bool,
    c_min: SNum,
    c_max: SNum,
}

fn main() {
    env::set_var("RUST_BACKTRACE", "1");

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
    for c in (233..=717).step_by(2) {
        // println!("{} {}", c, get_rule_sequence(c));

        let (seq, states) = get_rule_ac_sequence(c);
        print!("{} {} ", c, seq);
        for state in states {
            match state {
                AacState::A(curr_a, curr_c) => print!("{curr_a},{curr_c} "),
                AacState::Halt(n) => print!("Halt({n})"),
            }
        }
        println!();
    }
    println!();
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

    // for k in 1..=100000000000u64 {
    //     a_sim.step();
    //     if k % 1000000000 == 0 {
    //         println!("{:>13}", a_sim);
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
        if i >= 2 {
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

    for c_e in (0..2i64.pow(num_halvings)).step_by(2) {
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