use std::{env, str::FromStr};
use std::{fmt, fs, io, u64};
use npyz::{TypeStr, WriterBuilder};
use turing_machine::{check_transition_rule, BasicSimulator, BasicStepInfo, CheckerVerbosity, ConfigTransitionRule, State, Symbol, TMDirection, TuringMachine};
use strum_macros::Display;

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

#[derive(Clone, Copy)]
enum AacState {
    A(Num, Num),
    Halt(Num)
}

#[derive(Display, PartialEq, Eq, Clone, Copy)]
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
    for c in (472..=1442).step_by(2) {
    // for c in (233..=717).step_by(2) {
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
}