use npyz::{TypeStr, WriterBuilder};
use std::collections::HashMap;
use std::iter::Cycle;
use std::{env, str::FromStr};
use std::{fmt, fs, io, u64};
use strum_macros::Display;
use syn::token::Mod;

type Num = u128;
type SNum = i128;
const ONE: SNum = 1;
const TWO: SNum = 2;
const THREE: SNum = 3;

#[derive(Clone, Copy)]
enum AacState {
    A(Num, Num),
    Halt(Num),
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
    J,
}

struct AacSimulator {
    state: AacState,
    aac_steps: Num,
    a1_steps: Num,
    base_steps: Num,
}

impl AacSimulator {
    pub fn new() -> Self {
        AacSimulator {
            state: AacState::A(0, 1),
            aac_steps: 0,
            a1_steps: 0,
            base_steps: 2,
        }
    }

    pub fn step(&mut self) -> Option<AacRule> {
        use AacRule::*;
        use AacState::Halt;
        let (new_state, rule, new_steps) = if let AacState::A(a, c) = &self.state {
            self.aac_steps += 1;
            if c % 2 == 0 {
                if c >= a {
                    if a % 2 == 0 {
                        (Halt(a / 2 + c + 4), G, 3 * a * a + 5 * a + 9 * c + 24)
                    } else {
                        (
                            AacState::A(3 * a, c - a + 4),
                            I,
                            3 * a * a + 14 * c + 30 - 9 * a,
                        )
                    }
                } else {
                    (
                        AacState::A(a - c - 1, 3 * c / 2 + 2),
                        A,
                        3 * c * c + 8 * c + 5,
                    )
                }
            } else {
                if c >= a {
                    if a % 2 == 0 {
                        (
                            AacState::A(1, a / 2 + c + 2),
                            H,
                            3 * a * a + 3 * a + 5 * c + 11,
                        )
                    } else {
                        (AacState::A(3 * a + 2, c - a + 1), J, 3 * a * a + 5 * c + 6)
                    }
                } else {
                    if c + 1 == *a {
                        (Halt(3 * (c - 1) / 2 + 4), F, 3 * c * c + 8 * c + 6)
                    } else {
                        // c <= a - 2
                        if c % 4 == 1 {
                            (
                                AacState::A(a - c - 2, 3 * (c - 1) / 2 + 5),
                                B,
                                (6 * c * c + 31 * c + 37) / 2,
                            )
                        } else {
                            // c == 3 (mod 4)
                            if c + 2 == *a {
                                (AacState::A(3 * c + 8, 1), E, (6 * c * c + 37 * c + 63) / 2)
                            } else if c + 3 == *a {
                                (Halt(3 * (c - 1) / 2 + 7), D, (6 * c * c + 43 * c + 75) / 2)
                            } else {
                                // c <= a-4
                                (
                                    AacState::A(a - c - 4, 3 * (c - 1) / 2 + 8),
                                    C,
                                    3 * c * c + 29 * c + 65,
                                )
                            }
                        }
                    }
                }
            }
        } else {
            return None;
        };
        self.base_steps += new_steps;
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
        self.base_steps.fmt(f)?;
        write!(f, " | ")?;
        match self.state {
            AacState::A(a, c) => {
                write!(f, "A(")?;
                a.fmt(f)?;
                write!(f, ", ")?;
                c.fmt(f)?;
                write!(f, ")")?;
            }
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
    let mut a_sim = AacSimulator {
        state: AacState::A(1, c0),
        aac_steps: 0,
        a1_steps: 0,
        base_steps: 0,
    };

    loop {
        a_sim.step();
        match a_sim.state {
            AacState::Halt(_) => return None,
            AacState::A(1, c_new) => return Some(c_new - c0),
            _ => (),
        }
    }
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

fn main() {
    let mut sim = AacSimulator::new();
    println!("{sim}");

    let mut n = 3;
    let mut threshold = 2 * (3u128.pow(n) - n as u128 - 2);
    let mut prev_c = 0;
    let mut prev_steps = 0;

    for i in 1..=10000000000u64 {
        sim.step();
        if let AacState::A(1, c) = sim.state {
            if c > threshold {
                // println!("n: {n}, c: {prev_c}, steps: {prev_steps}");
                println!("[{prev_c}, {prev_steps}],");
                n += 1;
                threshold = 2 * (3u128.pow(n) - n as u128 - 2);
                // println!("{sim}");
            }
            prev_c = c;
            prev_steps = sim.base_steps;
        }
    }
}
