use std::ops::{Add, AddAssign};
use std::{collections::HashMap, fmt, str::FromStr, sync::OnceLock};
use std::error::Error;
use itertools::izip;
use strum_macros::EnumString;
use auto_ops::impl_op_ex;

/// Implement tape as two FIFO stacks; use Vec for the stacks
pub struct RLESimulator {
    pub left_tape: Vec<RLESymbol>,
    pub right_tape: Vec<RLESymbol>,
    pub dir: Direction,
    pub base_steps: usize,
    pub rle_steps: usize,
}

#[derive(Debug, Clone)]
pub enum SimError {
    HaltedError,
    UnreachableStateError,
}

impl fmt::Display for SimError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::HaltedError => write!(f, "Halted"),
            Self::UnreachableStateError => write!(f, "Unreachable state")
        }
    }
}

impl RLESimulator {
    pub fn new() -> Self {
        Self {
            left_tape: vec![RLESymbol(1)],
            right_tape: vec![],
            dir: Direction::Left,
            base_steps: 2,
            rle_steps: 0
        }
    }

    pub fn matches(&self, other: &Self) -> bool {
        if self.dir != other.dir {
            return false;
        }
        if self.right_tape != other.right_tape {
            return false;
        }
        let left_trimmed: Vec<_> = self.left_tape.iter().skip_while(|&&x| x == RLESymbol(0)).collect();
        let other_left_trimmed: Vec<_> = other.left_tape.iter().skip_while(|&&x| x == RLESymbol(0)).collect();
        if left_trimmed != other_left_trimmed {
            return false;
        }
        true
    }

    fn push_left(&mut self, n: u8) {
        self.left_tape.push(RLESymbol(n));
    }

    fn push_right(&mut self, n: u8) {
        self.right_tape.push(RLESymbol(n));
    }

    pub fn increment_left(&mut self) {
        match self.left_tape.pop() {
            Some(RLESymbol(m)) => self.push_left(m+1),
            None => self.push_left(1),
        }
    }

    /// RLE rules and # of base steps hard-coded here...
    pub fn step(&mut self) -> Result<(), SimError> {
        let new_base_steps: usize = match self.dir {
            Direction::Left => {
                match self.left_tape.pop() {
                    Some(RLESymbol(2)) => {
                        self.push_right(2);
                        3
                    }
                    Some(RLESymbol(1)) => {
                        self.push_right(1);
                        6
                    }
                    Some(RLESymbol(n @ 3..)) => {
                        self.push_left(n-3);
                        self.push_left(1);
                        self.dir = Direction::Right;
                        self.push_right(2);
                        4
                    }
                    Some(RLESymbol(0)) | None => {
                        self.increment_left();
                        self.dir = Direction::Right;
                        self.push_right(1);
                        1
                    }
                }
            }
            Direction::Right => {
                match self.right_tape.pop() {
                    Some(RLESymbol(2)) => {
                        match self.right_tape.pop() {
                            Some(RLESymbol(2)) => {
                                self.push_left(2);
                                self.push_left(2);
                                10
                            }
                            Some(RLESymbol(1)) => {
                                self.push_left(2);
                                self.push_left(1);
                                7
                            }
                            None => {
                                self.dir = Direction::Left;
                                self.push_right(2);
                                9
                            }
                            _ => unreachable!()
                        }
                    }
                    Some(RLESymbol(1)) => {
                        match self.right_tape.pop() {
                            Some(RLESymbol(1)) => {
                                self.increment_left();
                                self.push_left(2);
                                4
                            }
                            Some(RLESymbol(2)) => {
                                self.increment_left();
                                self.dir = Direction::Left;
                                self.push_right(1);
                                6
                            }
                            Some(RLESymbol(0)) | None => return Err(SimError::HaltedError),
                            Some(RLESymbol(3..)) => return Err(SimError::UnreachableStateError)
                        }
                    }
                    None => {
                        self.increment_left();
                        self.dir = Direction::Left;
                        2
                    }
                    Some(RLESymbol(3..)) | Some(RLESymbol(0)) => return Err(SimError::UnreachableStateError)
                }
            }
        };

        self.base_steps += new_base_steps;
        self.rle_steps += 1;
        Ok(())
    }
}

impl fmt::Display for RLESimulator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} | {}: ", self.rle_steps, self.base_steps)?;
        for symb in &self.left_tape {
            write!(f, "{}", symb.0)?;
        }
        match self.dir {
            Direction::Left => write!(f, " < ")?,
            Direction::Right => write!(f, " > ")?,
        }
        for symb in self.right_tape.iter().rev() {
            write!(f, "{}", symb.0)?;
        }

        Ok(())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct RLESymbol(pub u8);

#[derive(Debug, PartialEq, EnumString, Copy, Clone)]
pub enum Direction {
    #[strum(serialize = "L")]
    Left,
    #[strum(serialize = "R")]
    Right
}

impl fmt::Display for Direction {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::Left => write!(f, "<")?,
            Self::Right => write!(f, ">")?,
        }
        Ok(())
    }
}

static COUNTER_DEFINITION_FILE: &'static str = include_str!("counter_code_definition.txt");
static COUNTER_TRANSITION_FILE: &'static str = include_str!("counter_transition_rules.txt");

type Exp = u128;

#[derive(Debug, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
pub enum CounterSymbol {
    #[strum(serialize = "X", serialize = "x")]
    X(Exp),
    D,
    C0, C1, C2, C,
    R, L,
    P,
    F0, F1, F2, F3,
    G0, G1, G2,

    #[strum(disabled)]
    Block(CounterBlockType, Exp)
}

const LEFT_DEBRIS_DEF: &str = "C2 P x^2 D x C2 x^6 C2 x^9 C2 x^68 C x D x^33 C2 x^4 D x^27 C2 x^26 C2 x^44 D x^193 C x^19 D x^69 C1 x^227 C2 x^62 D x^55 C1 x^211 C2 x^1208 C2 x^2003 C1 x^90 D x^4023 C x^361 D x^2351 C x^26366 C x^2699 D x^2680 D x^15030 C1 x^9752 D D x^37542 C2 x^110 C2 x^3276 D x^3671 C1 x^3382 D x^14760 C0 x^5477 D x^15869 C1 x^7129 C2 x^189259 C x^58491 D D x^234225 C1 x^14 C1 x^8 C0 x^17 D D x^42 C0 x^54 C1 x^1096 C x^137 D x^1089 C x^327 D D x^4290 C0 x^197 D x^120 C1 x^426 C0 x^2637 D x^3718 C2 x^426 D x^16997 C1 x^1706 D x^21471 C1 x^2183 C x^106451 C1 D x^24011 C1 D x^182957 C1 D x^28035 C1 D x^14017 C2 D x^2794 C0 x D x^48418 C x^7 D x^42429 C2 x^28 D x^19778 C2 x^114 D x^11676 C2 x^458 D x^3190 C0 x^3756 C0 x^1157 D D x^55 D x^31758 C0 x^4855 D x^36 D x^23660 D x^34176 D x^656500 C x^250927 D x^138060 D x^103378 D x^25012 D x^12348 D x^27884 D x^2194 D D x^805994 C1 x^915326 D D x^160025 D x^75368 D x^5019243 C0 x^865 D x^197504 C2 x^3462 D x^92692 C1 x^45899 C0 x^15565 D x^38884 C x^62261 D x^90819 C x^485729 D x^625256 D x^6794309 C2 x^731366 D x^21623 C x^1144213 D x^16795620 C x^230309 D D x^55 D x^10382827 C1 x^901464 D x^1374756 C2 x^2455726 C2 x^2212892 D D x^4846062 C2 x^2669248 D D x^10696273 C1 D x^3075 C1 D x^1537 C1 D x^299 C1 D x^24725225 C1 D x^21175357 C1 D x^2472515 C1 D x^1236257 C1 D x^247243 C1 D x^14786855 C1 D x^4139075 C1 D x^2069537 C1 D x^413899 C1 D x^1735319 C1 D x^491555 C1 D x^245777 C2 D x^49146 C1 x^2 D x^285225 C1 x^8 D x^46363 C x^33 D x^74211 C1 x^132 D x^24803 C1 x^528 D x^13889 C1 x^4912 C x^13 D D x^55 D x^16028 C1 x^278 D x^14 D D x^55 D x^63754 C x^1401 D x^36 D x^6700 D D x^44045 C2 x^152 D D x^11639 D x^27826 C0 x^2147 D D x^7151 C x^127 C2 x^16715 C1 x^2 D x^3071 C2 x^8 D x^1520 C1 x^34 D x^231 C2 x^136 D x^30552 C1 x^546 D x^129993 C1 x^3127 C0 x^2579 D x^21524 D x^72314 C0 x^150871 C1 x^51970 D x^168244 D x^800372 C0 x^365655 C2 x^62770 D x^15796 C x^223257 D x^735876 C1 x^893026 D x^509692 D x^124196 D x^62098 D x^12412 D x^36058 D x^14948 D x^4204 D x^3074 D x^1538 D x^300 D x^426 D x^1229734 D x^36 D x^1164202 D D x^3655 D x^3917187 C x^16238487 D x^2916 D x^1458 D x^284 D x^113735990 C1 D x^65191315 C x D x^16057625 C0 x^3 D x^16041738 C2 x^14 D x^7407086 C x^59 D x^6703333 C0 x^235 D x^3299196 C1 x^942 D x^744335 C0 x^3767 D x^959802 C0 x^15069 D x^518964 C1 x^60278 D x^152847 C1 x^241112 D x^22774 C x^50721 D x^3277336 C x^202885 D x^491945 C2 x^126069 C x^2503207 D x^1510632 D x^10693544";
const J_DEF: &str = "C1 x^7640 D x^10345 C x^7639 D x^10347 C x^7635 D x^10355 C1 x^7618 D x^10389 C2 x^7550 D x^10524 C0 x^7279 D x^11066 C x^6197 D x^13231 C1 x^1866 D D x^7713 C0 x^95 C2 D";

#[derive(Debug, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
pub enum CounterBlockType {
    LeftDebris,
    A,
    B,
    G,
    J
}

pub fn parse_block_def(s: &str) -> Vec<CounterSymbol> {
    s.split(" ").map(|s2| {
        if s2.starts_with("x") {
            if s2 == "x" {
                CounterSymbol::X(1)
            } else {
                let (s3, s4) = s2.split_once("^").unwrap();
                assert!(s3 == "x");
                let exp = s4.parse::<Exp>().unwrap();
                CounterSymbol::X(exp)
            }
        } else {
            CounterSymbol::from_str(s2).unwrap()
        }
    }).collect()
}

pub fn left_block_definition() -> &'static HashMap<CounterBlockType, Vec<CounterSymbol>> {
    use CounterSymbol::*;
    use CounterBlockType::*;

    static MAP: OnceLock<HashMap<CounterBlockType, Vec<CounterSymbol>>> = OnceLock::new();
    MAP.get_or_init(|| {
        let mut m = HashMap::new();
        m.insert(LeftDebris, parse_block_def(LEFT_DEBRIS_DEF));
        m.insert(J, parse_block_def(J_DEF));
        m.insert(A, vec![C2, X(7640), D, X(10344)]);
        m.insert(B, vec![D, X(72142), D, X(3076), D, X(1538), D, X(300), D, X(30826)]);
        m.insert(G, vec![X(300), D, X(30826), D, X(72142), D, X(3076), D, X(1538), D]);
        m
    })
}

/// The symbols on the right tape are in reversed order compared with the left tape
pub fn right_block_definition() -> &'static HashMap<CounterBlockType, Vec<CounterSymbol>> {
    use CounterBlockType::*;

    static MAP: OnceLock<HashMap<CounterBlockType, Vec<CounterSymbol>>> = OnceLock::new();
    MAP.get_or_init(|| {
        let mut m = HashMap::new();
        m.insert(B, left_block_definition()[&B].iter().rev().cloned().collect());
        m.insert(G, left_block_definition()[&G].iter().rev().cloned().collect());
        m
    })
}

impl fmt::Display for CounterSymbol {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        use CounterSymbol::*;
        use CounterBlockType::*;
        use colored::Colorize;
        
        let s0 = match *self {
            X(_) => "x",
            Block(LeftDebris, _) => "[left debris]",
            Block(A, _) => "[a]",
            Block(B, _) => "[b]",
            Block(G, _) => "[G]",
            Block(J, _) => "[J]",
            _ => &format!("{:?}", self),
        };
        let s1 = match *self {
            C0 | C1 | C2 => s0.cyan().bold(),
            F0 | F1 | F2 | F3 | G0 | G1 | G2 => s0.blue(),
            C => s0.green().bold(),
            P => s0.purple(),
            L => s0.dimmed(),
            Block(A | LeftDebris, _) => s0.black().on_cyan().bold(),
            Block(J, _) => s0.black().on_green().bold(),
            Block(B | G, _) => s0.black().on_white().bold(),
            _ => s0.into(),
        };

        let s_exp = match *self {
            X(n) | Block(_, n) => {
                if n == 1 { "" }
                else { &format!("^{}", n)}
            },
            _ => "",
        };
        write!(f, "{}{}", s1, s_exp)
    }
}

#[derive(Debug, Copy, Clone)]
enum CounterRuleSymbol {
    Normal(CounterSymbol),
    XN,
}

impl CounterRuleSymbol {
    fn into_rle(&self, x_exp: Option<usize>) -> Vec<RLESymbol> {
        match self {
            Self::Normal(s) => {
                counter_to_rle().get(s).unwrap().to_owned()
            },
            Self::XN => {
                let v = counter_to_rle().get(&CounterSymbol::X(1)).unwrap();
                v.iter().cycle().take(v.len() * x_exp.unwrap()).cloned().collect()
            }
        }
    }
}

impl fmt::Display for CounterRuleSymbol {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Self::Normal(s) => write!(f, "{}", s)?,
            Self::XN => write!(f, "x^n")?,
        }
        Ok(())
    }
}

#[derive(Debug)]
struct CounterRuleState {
    lhs: Vec<CounterRuleSymbol>,
    rhs: Vec<CounterRuleSymbol>,
    dir: Direction,
}

impl fmt::Display for CounterRuleState {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.lhs.is_empty() {
            for s in &self.lhs {
                write!(f, "{} ", s)?;
            }
        }
        write!(f, "{}", self.dir)?;
        if !self.rhs.is_empty() {
            for s in &self.rhs {
                write!(f, " {}", s)?;
            }
        }
        Ok(())
    }
}

impl CounterRuleState {
    fn into_rle(&self, x_exp: Option<usize>) -> RLESimulator {
        let left_tape: Vec<_> = self.lhs.iter().flat_map(|s| s.into_rle(x_exp)).collect();
        let right_tape: Vec<_> = self.rhs.iter().flat_map(|s| s.into_rle(x_exp)).rev().collect();

        RLESimulator { left_tape, right_tape, dir: self.dir, base_steps: 0, rle_steps: 0 }
    }
}

#[derive(Debug)]
pub struct CounterRule {
    before: CounterRuleState,
    after: CounterRuleState,
    pub has_xn: bool
}

impl fmt::Display for CounterRule {
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} ==> {}", self.before, self.after)?;
        Ok(())
    }
}

pub fn counter_to_rle() -> &'static HashMap<CounterSymbol, Vec<RLESymbol>> {
    static MAP: OnceLock<HashMap<CounterSymbol, Vec<RLESymbol>>> = OnceLock::new();
    MAP.get_or_init(|| {
        let mut map = HashMap::new();
        for line in COUNTER_DEFINITION_FILE.lines() {
            let (p1, p2) = line.split_once(" ").unwrap();
            let c_symbol = if p1 == "x" { CounterSymbol::X(1) } else { CounterSymbol::from_str(p1).unwrap() };
            let rle_symbols: Vec<RLESymbol> = p2.chars().into_iter().map(|c| {
                RLESymbol(c.to_string().parse::<u8>().unwrap())
            }).collect();
            map.insert(c_symbol, rle_symbols);
        }
        map
    })
}

pub fn counter_transition_rules() -> &'static Vec<CounterRule> {
    static RULES: OnceLock<Vec<CounterRule>> = OnceLock::new();
    RULES.get_or_init(|| {
        let mut rules = Vec::new();
        for line in COUNTER_TRANSITION_FILE.split("\n").filter(|s| !s.is_empty()) {
            let (before_s, after_s) = line.split_once(" | ").unwrap();
            let (before, xn1) = parse_counter_rule_state(before_s);
            let (after, xn2) = parse_counter_rule_state(after_s);
            rules.push(CounterRule {
                before, after,
                has_xn: xn1 || xn2
            })
        }
        rules
    })
}

fn parse_counter_rule_state(s: &str) -> (CounterRuleState, bool) {
    let tokens: Vec<_> = s.split(" ").collect();
    let mut has_xn: bool = false;
    let mut lhs: Vec<CounterRuleSymbol> = Vec::new();
    let mut rhs: Vec<CounterRuleSymbol> = Vec::new();
    let mut dir: Option<Direction> = None;
    let mut passed_head = false;
    for token in tokens {
        match token {
            "<" => {
                passed_head = true;
                dir = Some(Direction::Left);
            },
            ">" => {
                passed_head = true;
                dir = Some(Direction::Right);
            },
            "xn" => {
                has_xn = true;
                (if passed_head { &mut rhs } else { &mut lhs }).push(CounterRuleSymbol::XN);
            },
            "x" => {
                (if passed_head { &mut rhs } else { &mut lhs }).push(CounterRuleSymbol::Normal(CounterSymbol::X(1)));
            }
            _ => {
                let symbol = CounterSymbol::from_str(token).unwrap();
                (if passed_head { &mut rhs } else { &mut lhs }).push(CounterRuleSymbol::Normal(symbol));
            }
        }
    }
    (CounterRuleState {
        lhs,
        rhs,
        dir: dir.unwrap()
    }, has_xn)
}

pub fn validate_counter_rule(rule: &CounterRule, x_exp: Option<usize>) -> Option<(usize, usize)> {
    let mut before_rle = rule.before.into_rle(x_exp);
    let after_rle = rule.after.into_rle(x_exp);
    let MAX_STEPS = 100;
    for _ in 0..MAX_STEPS {
        if before_rle.step().is_err() {
            println!("RLE error, {}", before_rle);
            return None;
        }
        if before_rle.matches(&after_rle) {
            return Some((before_rle.rle_steps, before_rle.base_steps));
        }
    }
    println!("failed to match");
    None
}

#[derive(Clone)]
pub struct CounterSimulator {
    pub left_tape: Vec<CounterSymbol>,
    pub right_tape: Vec<CounterSymbol>,
    pub dir: Direction,
    pub base_steps: u128,
    pub rle_steps: u128,
    pub self_steps: u64,
    pub do_strides: bool,
    pub do_uni_cycles: bool,
}

fn pop_n(tape: &mut Vec<CounterSymbol>, n: usize) {
    tape.truncate(tape.len() - n)
}

/// a0 + a1 * N
#[derive(Default, Clone, Copy)]
pub struct Binomial {
    pub a0: u128,
    pub a1: u128
}

impl fmt::Display for Binomial {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match (self.a0, self.a1) {
            (0, 0) => write!(f, "0"),
            (a0, 0) => write!(f, "{}", a0),
            (0, a1) => write!(f, "{}N", a1),
            (a0, a1) => write!(f, "{} + {}N", a0, a1)
        }
    }
}

impl_op_ex!(+ |a: &Binomial, b: &Binomial| -> Binomial {
    Binomial {
        a0: a.a0 + b.a0,
        a1: a.a1 + b.a1,
    }
});

impl_op_ex!(* |a: &Binomial, c: &u128| -> Binomial {
    Binomial {
        a0: a.a0 * c,
        a1: a.a1 * c,
    }
});

impl_op_ex!(+= |a: &mut Binomial, b: &Binomial| {
    a.a0 += b.a0;
    a.a1 += b.a1;
});

impl Binomial {
    pub fn checked_sub_const_assign(&mut self, c: u128) {
        self.a0 = self.a0.checked_sub(c).unwrap();
    }

    pub fn checked_add_const_assign(&mut self, c: u128) {
        self.a0 = self.a0.checked_add(c).unwrap();
    }
}

/// (rle_steps, base_steps)
#[derive(Debug, Clone)]
pub struct NSteps(Exp, Exp);

impl_op_ex!(+ |a: &NSteps, b: &NSteps| -> NSteps {
    NSteps(a.0 + b.0, a.1 + b.1)
});

impl_op_ex!(* |a: &NSteps, c: &Exp| -> NSteps {
    NSteps(a.0 * c, a.1 * c)
});

impl_op_ex!(+= |a: &mut NSteps, b: &NSteps| {
    a.0 += b.0;
    a.1 += b.1;
});

impl NSteps {
    pub fn checked_mul(&self, c: &Exp) -> Option<Self> {
        if let Some(r0) = self.0.checked_mul(*c) {
            if let Some(r1) = self.1.checked_mul(*c) {
                return Some(NSteps(r0, r1));
            }
        }
        None
    }

    pub fn checked_add(&self, x: &Self) -> Option<Self> {
        if let Some(r0) = self.0.checked_add(x.0) {
            if let Some(r1) = self.1.checked_add(x.1) {
                return Some(NSteps(r0, r1));
            }
        }
        None
    }
}

/// this calculates N_SINGLE_UNICYCLE_CONST and N_SINGLE_UNICYCLE_N
pub fn add_up_steps_for_one_uni_cycle() {
    let const_steps = N_X_LEFT * 13623629746 // S0
        + N_D_LEFT * 854899 // S1
        + N_C_LEFT * 71930 // S2
        + N_X_RIGHT * 13623370507 // S3
        + N_D_RIGHT * 854882 // S4
        + N_C_RIGHT * (71913 + 5) // S7, S11
        + N_C0_LEFT * 71911 // S8
        + N_C1_LEFT * 71932 // S9
        + N_C2_LEFT * 71930 // S10
        + (N_C_RIGHT // S12
            + N_F0_LEFT // S13
            + N_F1_LEFT // S14
            + N_F2_LEFT // S15
            + N_F3_LEFT // S16
            + N_C_RIGHT // S17
            + N_G0_LEFT // S18
            + N_G1_LEFT // S19
            + N_G2_LEFT // S20
        ) * 2
        + N_P_LEFT * 9 // S21
        + N_PX_RIGHT * 151338 // S23
        + N_PDX_RIGHT * 10 // S25
        + N_PCX_RIGHT * 8 // S26
        + N_PDP_RIGHT * 8 // S27
        + N_PDDX_RIGHT * 1; // S28

    let N_steps = N_X_LEFT * 53951 // S0
        + N_X_RIGHT * 53946 // S1
        + N_PX_RIGHT * 5; // S23

    println!("one uni cycle requires");
    println!("{:?} + {:?} * N steps (not counting strides on the right part)", const_steps, N_steps);
}

pub const N_SINGLE_UNICYCLE_CONST: NSteps = NSteps(40874209287, 217995063544);
pub const N_SINGLE_UNICYCLE_N: NSteps = NSteps(161853, 863216);

const N_X_LEFT: NSteps = NSteps(2, 6);
const N_D_LEFT: NSteps = NSteps(2, 9);
const N_C_LEFT: NSteps = NSteps(2, 12);
const N_P_LEFT: NSteps = NSteps(1, 3);
const N_C0_LEFT: NSteps = NSteps(3, 17);
const N_C1_LEFT: NSteps = NSteps(3, 11);
const N_C2_LEFT: NSteps = NSteps(3, 17);
const N_F0_LEFT: NSteps = NSteps(3, 17);
const N_F1_LEFT: NSteps = NSteps(3, 11);
const N_F2_LEFT: NSteps = NSteps(3, 17);
const N_F3_LEFT: NSteps = NSteps(3, 17);
const N_G0_LEFT: NSteps = NSteps(3, 17);
const N_G1_LEFT: NSteps = NSteps(3, 11);
const N_G2_LEFT: NSteps = NSteps(3, 17);
const N_G_BLOCK_LEFT: NSteps = NSteps(215774, 647337);

const N_X_RIGHT: NSteps = NSteps(1, 10);
const N_D_RIGHT: NSteps = NSteps(1, 7);
const N_R: NSteps = NSteps(1, 9);
const N_C_RIGHT: NSteps = NSteps(1, 4);
const N_PX_RIGHT: NSteps = NSteps(1, 10);
const N_PDX_RIGHT: NSteps = NSteps(4, 27);
const N_PCX_RIGHT: NSteps = NSteps(4, 19);
const N_PDP_RIGHT: NSteps = NSteps(4, 27);
const N_PDDX_RIGHT: NSteps = NSteps(14, 77);
const N_G_BLOCK_RIGHT: NSteps = NSteps(107887, 1078855);

/// this calculates N_G_BLOCK_LEFT and N_G_BLOCK_RIGHT
pub fn count_G_block_steps() {
    let mut n_D: Exp = 0;
    let mut n_x = 0;
    for symbol in &left_block_definition()[&CounterBlockType::G] {
        match symbol {
            CounterSymbol::D => n_D += 1,
            CounterSymbol::X(exp) => n_x += exp,
            _ => unreachable!()
        }
    }
    println!("{n_D} D's, {n_x} x's");

    let n_G_right = N_X_RIGHT * n_x + N_D_RIGHT * n_D;
    let n_G_left = N_X_LEFT * n_x + N_D_LEFT * n_D;
    println!("G< steps {:?}", n_G_left);
    println!(">G steps {:?}", n_G_right);
}

#[derive(Debug, Clone, Copy)]
pub enum CounterStepInfo {
    S(usize),
    S0(Exp),
    S3(Exp),
    S23(Exp),
    Stride { level: usize },
    UniCycle(Exp),
    GLeft,
    Expand(CounterBlockType),
}

impl CounterSimulator {
    pub fn new(do_strides: bool, do_uni_cycles: bool) -> Self {
        Self {
            left_tape: vec![CounterSymbol::L, CounterSymbol::C1],
            right_tape: vec![CounterSymbol::R],
            dir: Direction::Right,
            base_steps: 19,
            rle_steps: 5,
            self_steps: 0,
            do_strides,
            do_uni_cycles
        } 
    }

    fn consume_x(&mut self, dir: Direction) -> Result<(), SimError> {
        use CounterSymbol::X;
        use Direction::*;

        let s_opt = match dir {
            Left => self.left_tape.last_mut(),
            Right => self.right_tape.last_mut()
        };
        match s_opt {
            Some(X(1)) => {
                match dir {
                    Left => {self.left_tape.pop();}
                    Right => {self.right_tape.pop();}
                }
            }
            Some(X(n @ 2..)) => { *n -= 1; }
            _ => return Err(SimError::UnreachableStateError)
        }

        Ok(())
    }

    fn add_or_merge_x(&mut self, dir: Direction, nadd: Exp) {
        use CounterSymbol::X;
        use Direction::*;

        let s_opt = match dir {
            Left => self.left_tape.last_mut(),
            Right => self.right_tape.last_mut()
        };
        match s_opt {
            Some(X(n)) => { *n += nadd; }
            _ => match dir {
                Left => self.left_tape.push(X(nadd)),
                Right => self.right_tape.push(X(nadd)),
            }
        }
    }

    fn add_or_merge_block(&mut self, dir: Direction, block_t: CounterBlockType, nadd: Exp) {
        use CounterSymbol::Block;
        use Direction::*;

        let tape = match dir {
            Left => &mut self.left_tape,
            Right => &mut self.right_tape,
        };

        if let Some(Block(block_t0, n)) = tape.last_mut() {
            if *block_t0 == block_t {
                *n += nadd;
                return;
            }
        }

        tape.push(Block(block_t, nadd));
    }

    fn basic_counter_step(&mut self) -> Result<(CounterStepInfo, NSteps), SimError> {
        use CounterSymbol::*;
        use CounterStepInfo::*;
        use CounterBlockType::*;
        use Direction::*;

        let (step_info, new_steps): (CounterStepInfo, NSteps) = match self.dir {
            Left => match self.left_tape.pop() {
                // 0: x^n < ==> < x^n (2 * n, 6 * n)
                Some(X(n)) => {
                    self.add_or_merge_x(Right, n);
                    if self.do_uni_cycles {
                        if self.right_tape.ends_with(&right_block_definition()[&G]) {
                            pop_n(&mut self.right_tape, right_block_definition()[&G].len());
                            self.add_or_merge_block(Right, G, 1);
                        }
                    }
                    (S0(n), N_X_LEFT * n)
                }
                // 1: D < ==> < D (2, 9)
                Some(D) => {
                    self.right_tape.push(D);
                    (S(1), N_D_LEFT)
                }
                // 2: C < ==> < C (2, 12)
                Some(C) => {
                    self.right_tape.push(C);
                    (S(2), N_C_LEFT)
                }
                // 6: L < C x ==> L C1 D > P (5, 22)
                Some(L) => {
                    match self.right_tape.pop() {
                        Some(C) => {
                            self.consume_x(Right)?;
                            self.left_tape.extend_from_slice(&[L, C1, D]);
                            self.dir = Right;
                            self.right_tape.push(P);
                            (S(6), NSteps(5, 22))
                        },
                        _ => return Err(SimError::UnreachableStateError),
                    }
                }
                // 8: C0 < ==> C1 x > (3, 17)
                Some(C0) => {
                    self.left_tape.extend_from_slice(&[C1, X(1)]);
                    self.dir = Right;
                    (S(8), N_C0_LEFT)
                }
                // 9: C1 < ==> C2 > (3, 11)
                Some(C1) => {
                    self.left_tape.push(C2);
                    self.dir = Right;
                    (S(9), N_C1_LEFT)
                }
                // 10: C2 < ==> C x > (3, 17)
                Some(C2) => {
                    self.left_tape.extend_from_slice(&[C, X(1)]);
                    self.dir = Right;
                    (S(10), N_C2_LEFT)
                }
                // 13: F0 < ==> F1 x > (3, 17)
                Some(F0) => {
                    self.left_tape.extend_from_slice(&[F1, X(1)]);
                    self.dir = Right;
                    (S(13), N_F0_LEFT)
                }
                // 14: F1 < ==> F2 > (3, 11)
                Some(F1) => {
                    self.left_tape.push(F2);
                    self.dir = Right;
                    (S(14), N_F1_LEFT)
                }
                // 15: F2 < ==> F3 x > (3, 17)
                Some(F2) => {
                    self.left_tape.extend_from_slice(&[F3, X(1)]);
                    self.dir = Right;
                    (S(15), N_F2_LEFT)
                }
                // 16: x F3 < ==> P C1 D > (3, 17)
                Some(F3) => {
                    self.consume_x(Left)?;
                    self.left_tape.extend_from_slice(&[P, C1, D]);
                    self.dir = Right;
                    (S(16), N_F3_LEFT)
                }
                // 18: G0 < ==> G1 x > (3, 17)
                Some(G0) => {
                    self.left_tape.extend_from_slice(&[G1, X(1)]);
                    self.dir = Right;
                    (S(18), N_G0_LEFT)
                }
                // 19: G1 < ==> G2 > (3, 11)
                Some(G1) => {
                    self.left_tape.push(G2);
                    self.dir = Right;
                    (S(19), N_G1_LEFT)
                }
                // 20: G2 < ==> P D x > (3, 17)
                Some(G2) => {
                    self.left_tape.extend_from_slice(&[P, D, X(1)]);
                    self.dir = Right;
                    (S(20), N_G2_LEFT)
                }
                // 21: P < ==> < P (1, 3)
                Some(P) => {
                    self.right_tape.push(P);
                    (S(21), N_P_LEFT)
                }
                // J < ==> expanded-J < (0, 0)
                Some(Block(J, 1)) => {
                    self.left_tape.extend_from_slice(&left_block_definition()[&J]);
                    (Expand(J), NSteps(0, 0))
                }
                // G^n < ==> < G^n
                Some(Block(G, exp)) => {
                    self.add_or_merge_block(Right, G, exp);
                    (GLeft, N_G_BLOCK_LEFT * exp)
                }
                _ => return Err(SimError::UnreachableStateError),
            },
            Right => match self.right_tape.pop() {
                // 3: > x^n ==> x^n > (1 * n, 10 * n)
                Some(X(n)) => {
                    self.add_or_merge_x(Left, n);
                    (S3(n), N_X_RIGHT * n)
                }
                // 4: > D ==> D > (1, 7)
                Some(D) => {
                    self.left_tape.push(D);
                    if self.do_uni_cycles {
                        if self.left_tape.ends_with(&left_block_definition()[&J]) {
                            pop_n(&mut self.left_tape, left_block_definition()[&J].len());
                            self.left_tape.push(Block(J, 1));
                        } else if self.left_tape.ends_with(&left_block_definition()[&G]) {
                            pop_n(&mut self.left_tape, left_block_definition()[&G].len());
                            self.add_or_merge_block(Left, G, 1);
                        }
                    }

                    (S(4), N_D_RIGHT)
                }
                // 5: > R ==> < R (1, 9)
                Some(R) => {
                    self.right_tape.push(R);
                    self.dir = Left;
                    (S(5), N_R)
                }
                Some(C) => {
                    let type_id = match self.left_tape.last() {
                        // 7: x > C ==> C0 > (1, 4)
                        Some(X(_)) => {
                            self.consume_x(Left)?;

                            if self.do_uni_cycles {
                                if self.left_tape.ends_with(&left_block_definition()[&A]) {
                                    pop_n(&mut self.left_tape, left_block_definition()[&A].len());
                                    self.add_or_merge_block(Left, A, 1);
                                }
                            }

                            self.left_tape.push(C0);
                            7
                        }
                        // 11: D > C ==> P x > (1, 4)
                        Some(D) => {
                            self.left_tape.pop();
                            self.left_tape.extend_from_slice(&[P, X(1)]);
                            11
                        }
                        // 12: C2 > C ==> F0 > (1, 4)
                        Some(C2) => { *self.left_tape.last_mut().unwrap() = F0; 12 }
                        // 17: C0 > C ==> G0 > (1, 4)
                        Some(C0) => { *self.left_tape.last_mut().unwrap() = G0; 17 }
                        _ => return Err(SimError::UnreachableStateError)
                    };
                    (S(type_id), N_C_RIGHT)
                }
                Some(P) => match self.right_tape.pop() {
                    // 22: > P P ==> x > (1, 10)
                    Some(P) => {
                        self.add_or_merge_x(Left, 1);
                        (S(22), NSteps(1, 10))
                    }
                    // 23: > P x^n ==> x^n > P (1 * n, 10 * n)
                    Some(X(n)) => {
                        self.add_or_merge_x(Left, n);
                        self.right_tape.push(P);
                        (S23(n), N_PX_RIGHT * n)
                    }
                    // 24: > P R ==> < C x R (16, 89)
                    Some(R) => {
                        self.dir = Left;
                        self.right_tape.extend_from_slice(&[R, X(1), C]);
                        (S(24), NSteps(16, 89))
                    }
                    // 26: > P C x ==> < P D P (4, 19)
                    Some(C) => {
                        self.consume_x(Right)?;
                        self.dir = Left;
                        self.right_tape.extend_from_slice(&[P, D, P]);
                        (S(26), N_PCX_RIGHT)
                    }
                    Some(D) => match self.right_tape.last() {
                        // 25: > P D x ==> C1 D > P (4, 27)
                        Some(X(_)) => {
                            self.consume_x(Right)?;
                            self.left_tape.extend_from_slice(&[C1, D]);
                            self.right_tape.push(P);
                            (S(25), N_PDX_RIGHT)
                        }
                        // "S30": > P D R ==> C1 < P R (7, 35)
                        Some(R) => {
                            self.left_tape.push(C1);
                            self.dir = Left;
                            self.right_tape.push(P);
                            (S(30), NSteps(7, 35))
                        }
                        _ => match self.right_tape.pop() {
                            // 27: > P D P ==> C1 D > (4, 27)
                            Some(P) => {
                                self.left_tape.extend_from_slice(&[C1, D]);
                                (S(27), N_PDP_RIGHT)
                            }
                            // 28: > P D D x ==> C2 C1 D > (14, 77)
                            Some(D) => {
                                self.consume_x(Right)?;
                                self.left_tape.extend_from_slice(&[C2, C1, D]);
                                (S(28), N_PDDX_RIGHT)
                            }
                            // 29: > P D C x ==> G1 D > P (5, 31)
                            Some(C) => {
                                self.consume_x(Right)?;
                                self.left_tape.extend_from_slice(&[G1, D]);
                                self.right_tape.push(P);
                                (S(29), NSteps(5, 31))
                            }
                            _ => return Err(SimError::UnreachableStateError)
                        }
                    }
                    _ => return Err(SimError::UnreachableStateError)
                },
                // > G^n ==> G^n >
                Some(Block(G, exp)) => {
                    self.add_or_merge_block(Left, G, exp);
                    (GLeft, N_G_BLOCK_RIGHT * exp)
                }
                _ => return Err(SimError::UnreachableStateError)
            }
        };
        Ok((step_info, new_steps))
    }

    pub fn can_do_stride(&self) -> bool {
        use CounterSymbol::*;
        use Direction::*;

        if self.dir == Left {
            return false;
        }

        match self.right_tape.last() {
            Some(X(_)) | Some(D) => (),
            _ => return false,
        }

        for symb in self.right_tape.iter().rev() {
            match symb {
                X(_) | D | C | R => continue,
                _ => return false,
            }
        }

        let rtape_rev: Vec<CounterSymbol> = self.right_tape.iter().rev().cloned().collect();
        let split: Vec<_> = rtape_rev.split(|&s| s == C).collect();

        // w_i = (x|D)*

        // > w0 R ==> < w0 R
        // stride level 0
        if split.len() == 1 {
            return true;
        } else {
            let mut powers_4: Vec<Exp> = vec![1];

            // Verify that there are enough x's to the left of each C
            for (i, &part) in (&split[..split.len()-1]).iter().enumerate() {
                let n_eat = if i == 0 {
                    1
                } else {
                    let n_new = powers_4[i-1] * 4;
                    powers_4.push(n_new);
                    n_new
                };

                match part.split_last() {
                    Some((X(exp), _)) => if *exp < n_eat { return false },
                    _ => return false,
                }
            }
        }

        true
    }

    /// Does a stride if possible. Returns None if stride not possible.
    fn try_stride(&mut self) -> Option<(usize, NSteps)> {
        use CounterSymbol::*;
        use Direction::*;

        if self.dir == Left {
            return None;
        }

        match self.right_tape.last() {
            Some(X(_)) | Some(D) => (),
            Some(Block(CounterBlockType::G, _)) => (),
            _ => return None,
        }

        for symb in self.right_tape.iter().rev() {
            match symb {
                X(_) | D | C | Block(CounterBlockType::G, _) | R => continue,
                _ => return None,
            }
        }

        let rtape_rev: Vec<CounterSymbol> = self.right_tape.iter().rev().cloned().collect();
        let split: Vec<_> = rtape_rev.split(|&s| s == C).collect();

        // w_i = (x|D)*

        // > w0 R ==> < w0 R
        // stride level 0
        if split.len() == 1 {
            let mut n_x = 0;
            let mut n_D = 0;
            let mut n_G = 0;
            for symb in split[0] {
                match symb {
                    X(n) => n_x += n,
                    D => n_D += 1,
                    Block(CounterBlockType::G, n) => n_G += n,
                    R => continue,
                    _ => unreachable!()
                }
            }
            self.dir = Left;
            Some((0, (N_X_RIGHT+N_X_LEFT) * n_x + (N_D_RIGHT+N_D_LEFT) * n_D
                + (N_G_BLOCK_LEFT+N_G_BLOCK_RIGHT) * n_G + N_R))
        } else {
            let mut powers_4: Vec<Exp> = vec![1];

            // Verify that there are enough x's to the left of each C
            for (i, &part) in (&split[..split.len()-1]).iter().enumerate() {
                let n_eat = if i == 0 {
                    1
                } else {
                    let n_new = powers_4[i-1] * 4;
                    powers_4.push(n_new);
                    n_new
                };

                match part.split_last() {
                    Some((X(exp), _)) => if *exp < n_eat { return None },
                    _ => return None,
                }
            }
            powers_4.push(powers_4.last().unwrap() * 4);

            // > w0 x C     w1 x^4 C     ... w_n x^4^n C           w_{n+1} R ==>
            // < w0   C x^2 w1     C x^8 ... w_n       C x^(2*4^n) w_{n+1} R

            // stride level is n+1, since there are n+1 C's

            // count the number of x's and D's in each w_i; the x's to be eaten by a C do not count
            let n = split.len() - 2;
            let mut n_x: Vec<Exp> = Vec::new();
            let mut n_D: Vec<u32> = Vec::new();
            let mut n_G: Vec<Exp> = Vec::new();
            for (i, &part) in split.iter().enumerate() {
                let mut curr_n_x = 0;
                let mut curr_n_D = 0;
                let mut curr_n_G = 0;
                for symb in part {
                    match symb {
                        X(exp) => curr_n_x += exp,
                        D => curr_n_D += 1,
                        Block(CounterBlockType::G, exp) => curr_n_G += exp,
                        R => (),
                        _ => unreachable!()
                    }
                }
                if i <= n {
                    curr_n_x -= powers_4[i];
                }
                n_x.push(curr_n_x);
                n_D.push(curr_n_D);
                n_G.push(curr_n_G);
            }

            // actually edit the parts to delete and add x's
            let mut parts: Vec<_> = split.into_iter().map(|s| s.to_vec()).collect();
            for i in 0..=n {
                let X(exp) = parts[i].last_mut().unwrap() else { unreachable!() };
                if *exp > powers_4[i] {
                    *exp -= powers_4[i];
                } else if *exp == powers_4[i] {
                    parts[i].pop();
                } else {
                    unreachable!()
                }

                if let X(exp) = parts[i+1].first_mut().unwrap() {
                    *exp += powers_4[i] * 2;
                } else {
                    parts[i+1].insert(0, X(powers_4[i] * 2));
                }
            }

            let mut rtape_new: Vec<CounterSymbol> = Vec::new();
            rtape_new.extend(parts.pop().unwrap().into_iter().rev());
            for part in parts.drain(..).rev() {
                rtape_new.push(C);
                rtape_new.extend(part.into_iter().rev());
            }

            self.right_tape = rtape_new;
            self.dir = Left;

            // step count
            let mut w_steps = NSteps(0, 0);
            assert!(powers_4.len() >= n_x.len());
            for (pow, curr_n_x, curr_n_D, curr_n_G) in izip!(&powers_4, n_x, n_D, n_G) {
                w_steps += ((N_X_RIGHT+N_X_LEFT) * curr_n_x
                    + (N_D_RIGHT+N_D_LEFT) * curr_n_D as u128
                    + (N_G_BLOCK_LEFT+N_G_BLOCK_RIGHT) * curr_n_G) * pow;
            }
            let R_steps = N_R * powers_4[n+1];
            
            let a1 = powers_4[n+1] - 1;
            let a2 = a1 / 3;
            let p16 = 1u128.checked_shl(4 * (n as u32 + 1)).unwrap();
            let rep_x_both = ((p16 - 1) / 15 - a2) * 9 / 2;
            let rep_x_left = a2 * 4;
            let C_steps = (N_X_RIGHT+N_X_LEFT) * rep_x_both + N_X_RIGHT * a1 + N_X_LEFT * rep_x_left
                + (N_C0_LEFT + N_C1_LEFT + N_C2_LEFT + N_C_LEFT + N_C_RIGHT) * a2;           

            Some((n+1, w_steps + R_steps + C_steps))
        }
    }

    fn multi_stride(&mut self, k: Exp) -> Result<(usize, NSteps), SimError> {
        use CounterSymbol::*;
        use Direction::*;

        if self.dir == Left {
            return Err(SimError::UnreachableStateError);
        }

        match self.right_tape.last() {
            Some(X(_)) | Some(D) => (),
            _ => return Err(SimError::UnreachableStateError),
        }

        for symb in self.right_tape.iter().rev() {
            match symb {
                X(_) | D | C | R => continue,
                _ => return Err(SimError::UnreachableStateError),
            }
        }

        let rtape_rev: Vec<CounterSymbol> = self.right_tape.iter().rev().cloned().collect();
        let split: Vec<_> = rtape_rev.split(|&s| s == C).collect();

        // w_i = (x|D)*

        // > w0 R ==> < w0 R
        // stride level 0
        if split.len() == 1 {
            let mut n_x = 0;
            let mut n_D = 0;
            for symb in split[0] {
                match symb {
                    X(n) => n_x += n,
                    D => n_D += 1,
                    R => continue,
                    _ => unreachable!()
                }
            }
            self.dir = Left;
            Ok((0, ((N_X_RIGHT+N_X_LEFT) * n_x + (N_D_RIGHT+N_D_LEFT) * n_D + N_R) * k))
        } else {
            let mut k_powers_4: Vec<Exp> = vec![k];

            // Verify that there are enough x's to the left of each C
            for (i, &part) in (&split[..split.len()-1]).iter().enumerate() {
                let n_eat = if i == 0 {
                    k
                } else {
                    let n_new = k_powers_4[i-1] * 4;
                    k_powers_4.push(n_new);
                    n_new
                };

                match part.split_last() {
                    Some((X(exp), _)) => if *exp < n_eat { return Err(SimError::UnreachableStateError) },
                    _ => return Err(SimError::UnreachableStateError),
                }
            }
            k_powers_4.push(k_powers_4.last().unwrap() * 4);

            // > w0 x^k C      w1 x^4k C      ... w_n x^{k*4^n} C            w_{n+1} R ==>
            // < w0     C x^2k w1      C x^8k ... w_n           C x^(2k*4^n) w_{n+1} R

            // stride level is n+1, since there are n+1 C's

            // count the number of x's and D's in each w_i; the x's to be eaten by a C do not count
            let n = split.len() - 2;
            let mut n_x: Vec<Exp> = Vec::new();
            let mut n_D: Vec<u32> = Vec::new();
            for (i, &part) in split.iter().enumerate() {
                let mut curr_n_x = 0;
                let mut curr_n_D = 0;
                for symb in part {
                    match symb {
                        X(exp) => curr_n_x += exp,
                        D => curr_n_D += 1,
                        R => (),
                        _ => unreachable!()
                    }
                }
                if i <= n {
                    curr_n_x -= k_powers_4[i];
                }
                n_x.push(curr_n_x);
                n_D.push(curr_n_D);
            }

            // actually edit the parts to delete and add x's
            let mut parts: Vec<_> = split.into_iter().map(|s| s.to_vec()).collect();
            for i in 0..=n {
                let X(exp) = parts[i].last_mut().unwrap() else { unreachable!() };
                if *exp > k_powers_4[i] {
                    *exp -= k_powers_4[i];
                } else if *exp == k_powers_4[i] {
                    parts[i].pop();
                } else {
                    unreachable!()
                }

                if let X(exp) = parts[i+1].first_mut().unwrap() {
                    *exp += k_powers_4[i] * 2;
                } else {
                    parts[i+1].insert(0, X(k_powers_4[i] * 2));
                }
            }

            let mut rtape_new: Vec<CounterSymbol> = Vec::new();
            rtape_new.extend(parts.pop().unwrap().into_iter().rev());
            for part in parts.drain(..).rev() {
                rtape_new.push(C);
                rtape_new.extend(part.into_iter().rev());
            }

            self.right_tape = rtape_new;
            // self.dir = Left; // handle direction change elsewhere???

            // step count
            let mut w_steps = NSteps(0, 0);
            assert!(k_powers_4.len() >= n_x.len());
            for (k_pow, curr_n_x, curr_n_D) in izip!(&k_powers_4, n_x, n_D) {
                w_steps += ((N_X_RIGHT+N_X_LEFT) * curr_n_x + (N_D_RIGHT+N_D_LEFT) * curr_n_D as u128) * k_pow;
            }
            let R_steps = N_R * k_powers_4[n+1];

            let p4 = 1u128 << (2 * (n as u32 + 1));
            let sum_m3 = (p4 - 1) * k;
            let sum_m = sum_m3 / 3;
            let sum_m4 = sum_m * 4;
            let p16 = 1u128.checked_shl(4 * (n as u32 + 1)).unwrap();
            let sum_msq = (p16 - 1).checked_mul(k*k).unwrap() / 15;
            let rep_x_both = (sum_msq - sum_m) * 9 / 2;
            let rep_x_left = sum_m4;
            let C_steps = (N_X_RIGHT+N_X_LEFT) * rep_x_both + N_X_RIGHT * sum_m3 + N_X_LEFT * rep_x_left
            + (N_C0_LEFT + N_C1_LEFT + N_C2_LEFT + N_C_LEFT + N_C_RIGHT) * sum_m;

            Ok((n+1, w_steps + R_steps + C_steps))
        }
    }

    fn num_strides_possible(&self) -> Exp {
        use CounterSymbol::*;
        use Direction::*;

        if self.dir == Left {
            return 0;
        }

        match self.right_tape.last() {
            Some(X(_)) | Some(D) => (),
            _ => return 0,
        }

        for symb in self.right_tape.iter().rev() {
            match symb {
                X(_) | D | C | R => continue,
                _ => return 0,
            }
        }

        let rtape_rev: Vec<CounterSymbol> = self.right_tape.iter().rev().cloned().collect();
        let split: Vec<_> = rtape_rev.split(|&s| s == C).collect();

        if split.len() == 1 {
            return u128::MAX;
        } else {
            let mut powers_4: Vec<Exp> = vec![1];
            let mut max_n = u128::MAX;

            for (i, &part) in (&split[..split.len()-1]).iter().enumerate() {
                let n_eat = if i == 0 {
                    1
                } else {
                    let n_new = powers_4[i-1] * 4;
                    powers_4.push(n_new);
                    n_new
                };

                match part.split_last() {
                    Some((X(exp), _)) => {
                        if *exp < n_eat {
                            return 0;
                        } else {
                            max_n = max_n.min(*exp / n_eat);
                        }
                    },
                    _ => return 0,
                }
            }
            return max_n;
        }
    }

    /// Does uni-cycles if possible. Returns None if uni-cycle not possible.
    fn try_uni_cycle(&mut self) -> Option<(Exp, NSteps)> {
        use CounterSymbol::*;
        use CounterBlockType::*;
        use Direction::*;

        const UNI_CYCLE_P: Exp = 53946;
        const UNI_CYCLE_T: Exp = 215779;

        //     J x^n      C1 D >            r   --->
        // F^k J x^(n-kP) C1 D > G^k s^{kT}(r)
        if self.dir == Left {
            return None;
        }

        if let [.., Block(J, 1), X(x_exp), C1, D] = self.left_tape.as_slice() {
            if *x_exp < UNI_CYCLE_P {
                return None;
            }
            let max_strides = self.num_strides_possible();
            if max_strides < UNI_CYCLE_T {
                return None;
            }

            let max_cycles_left = *x_exp / UNI_CYCLE_P;
            let max_cycles_right = max_strides / UNI_CYCLE_T;
            let num_cycles = max_cycles_left.min(max_cycles_right);

            // count the steps and do the strides
            let N = *x_exp - UNI_CYCLE_P;
            let N_final = *x_exp - UNI_CYCLE_P * num_cycles;

            let left_steps_const = N_SINGLE_UNICYCLE_CONST.checked_mul(&num_cycles).unwrap();
            let left_N_occurrences = (N + N_final).checked_mul(num_cycles).unwrap() / 2;
            let left_steps_N = N_SINGLE_UNICYCLE_N.checked_mul(&left_N_occurrences).unwrap();

            let G_occurrences = (num_cycles.checked_mul(num_cycles - 1).unwrap() / 2)
                                            .checked_mul(UNI_CYCLE_T).unwrap();
            let G_steps = (N_G_BLOCK_LEFT + N_G_BLOCK_RIGHT).checked_mul(&G_occurrences).unwrap();

            let (_, stride_steps) = self.multi_stride(num_cycles * UNI_CYCLE_T).unwrap();
            let total_steps = left_steps_const.checked_add(&left_steps_N).unwrap()
                .checked_add(&G_steps).unwrap()
                .checked_add(&stride_steps).unwrap();

            // finish updating the tape
            pop_n(&mut self.left_tape, 4);
            self.add_or_merge_block(Left, A, num_cycles);
            self.left_tape.push(Block(J, 1));
            if N_final > 0 {
                self.left_tape.push(X(N_final));
            }
            self.left_tape.extend_from_slice(&[C1, D]);

            self.add_or_merge_block(Right, G, num_cycles);

            return Some((num_cycles, total_steps))
        }
        None
    }

    pub fn step(&mut self) -> Result<CounterStepInfo, SimError> {
        if self.do_uni_cycles {
            if let Some((n_repeats, NSteps(new_rle_steps, new_base_steps))) = self.try_uni_cycle() {
                self.rle_steps = self.rle_steps.checked_add(new_rle_steps).unwrap();
                self.base_steps = self.base_steps.checked_add(new_base_steps).unwrap();
                self.self_steps += 1;
                return Ok(CounterStepInfo::UniCycle(n_repeats));
            }
        }

        if self.do_strides {
            if let Some((stride_level_val, NSteps(new_rle_steps, new_base_steps))) = self.try_stride() {
                self.rle_steps = self.rle_steps.checked_add(new_rle_steps).unwrap();
                self.base_steps = self.base_steps.checked_add(new_base_steps).unwrap();
                self.self_steps += 1;
                return Ok(CounterStepInfo::Stride { level: stride_level_val });
            }
        }

        let (basic_step_info, NSteps(new_rle_steps, new_base_steps)) = self.basic_counter_step()?;
        self.rle_steps = self.rle_steps.checked_add(new_rle_steps).unwrap();
        self.base_steps = self.base_steps.checked_add(new_base_steps).unwrap();
        self.self_steps += 1;
        Ok(basic_step_info)
    }

    pub fn rewrite_with_blocks(&mut self, left_block_types: &Vec<CounterBlockType>, right_block_types: &Vec<CounterBlockType>) {
        for t in left_block_types {
            self.left_tape = replace(&self.left_tape, left_block_definition()[t].as_slice(), &[CounterSymbol::Block(*t, 1)]);
            collapse_block_runs(&mut self.left_tape, *t);
        }

        for t in right_block_types {
            self.right_tape = replace(&self.right_tape, right_block_definition()[t].as_slice(), &[CounterSymbol::Block(*t, 1)]);
            collapse_block_runs(&mut self.right_tape, *t);
        }
    }
}

fn replace<T>(source: &[T], from: &[T], to: &[T]) -> Vec<T>
where
    T: Clone + PartialEq
{
    let mut result = source.to_vec();
    let from_len = from.len();
    let to_len = to.len();

    let mut i = 0;
    while i + from_len <= result.len() {
        if result[i..].starts_with(from) {
            result.splice(i..i + from_len, to.iter().cloned());
            i += to_len;
        } else {
            i += 1;
        }
    }

    result
}

fn collapse_block_runs(v: &mut Vec<CounterSymbol>, t: CounterBlockType) {
    use CounterSymbol::Block;
    let mut i = 0;
    while i + 1 < v.len() {
        if let Some(Block(t2, _)) = v.get(i) {
            if *t2 == t {
                let mut i2 = i + 1;
                let mut n_next = 0;
                loop {
                    if let Some(Block(t3, n)) = v.get(i2) {
                        if *t3 == t {
                            n_next += n;
                            i2 += 1;
                        } else { break; }
                    } else { break; }
                }

                if i2 > i + 1 {
                    v.drain(i+1..i2);
                    let Some(Block(_, n0)) = v.get_mut(i) else { unreachable!() };
                    *n0 += n_next;
                }
            }       
        }

        i += 1;
    }
}

impl fmt::Display for CounterSimulator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        
        self.self_steps.fmt(f)?;
        write!(f, " | {} | {}: ", self.rle_steps, self.base_steps)?;
        for symb in &self.left_tape {
            write!(f, "{} ", symb)?;
        }
        match self.dir {
            Direction::Left => write!(f, "{}", "<".red().bold())?,
            Direction::Right => write!(f, "{}", ">".red().bold())?,
        }
        for symb in self.right_tape.iter().rev() {
            write!(f, " {}", symb)?;
        }

        Ok(())
    }
}

fn measure_partial_stride(counts: &mut HashMap<usize, u128>, n_counts: &mut HashMap<usize, Binomial>, 
    rtape: &Vec<CounterSymbol>, r_xnr_idx: usize, N0: u128, N1: u128) {
    use CounterSymbol::*;
    
    let mut rtape_rev: Vec<CounterSymbol> = rtape[r_xnr_idx+1..].iter().rev().cloned().collect(); // chop off the right block
    rtape_rev.push(R); // we will also count the number of times the head bounces off of this substitute R - this is a way to count # strides to the right
    let split: Vec<_> = rtape_rev.split(|&s| s == C).collect();

    // w_i = (x|D)*

    // > w0 R ==> < w0 R
    // stride level 0
    if split.len() == 1 {
        let mut n_x: Binomial = Binomial::default();
        let mut n_D = 0;
        for symb in split[0] {
            match symb {
                X(n) => n_x += n_infer(*n, N0, N1),
                D => n_D += 1,
                R => continue,
                _ => unreachable!()
            }
        }

        *n_counts.entry(0).or_default() += n_x; // N_X_LEFT
        *n_counts.entry(3).or_default() += n_x; // N_X_RIGHT

        *counts.entry(4).or_default() += n_D; // N_D_RIGHT
        *counts.entry(1).or_default() += n_D; // N_D_LEFT
        *counts.entry(5).or_default() += 1;   // right stride
    } else {
        let mut powers_4: Vec<u128> = vec![1];

        // Verify that there are enough x's to the left of each C
        for (i, &part) in (&split[..split.len()-1]).iter().enumerate() {
            let n_eat = if i == 0 {
                1
            } else {
                let n_new = powers_4[i-1] * 4;
                powers_4.push(n_new);
                n_new
            };

            match part.split_last() {
                Some((X(exp), _)) => if *exp < n_eat { unreachable!() },
                _ => unreachable!(),
            }
        }
        powers_4.push(powers_4.last().unwrap() * 4);

        // > w0 x C     w1 x^4 C     ... w_n x^4^n C           w_{n+1} R ==>
        // < w0   C x^2 w1     C x^8 ... w_n       C x^(2*4^n) w_{n+1} R

        // stride level is n+1, since there are n+1 C's

        // count the number of x's and D's in each w_i; the x's to be eaten by a C do not count
        let n = split.len() - 2;
        let mut n_x: Vec<Binomial> = Vec::new();
        let mut n_D: Vec<u32> = Vec::new();
        for (i, &part) in split.iter().enumerate() {
            let mut curr_n_x = Binomial::default();
            let mut curr_n_D = 0;
            for symb in part {
                match symb {
                    X(exp) => curr_n_x += n_infer(*exp, N0, N1),
                    D => curr_n_D += 1,
                    R => (),
                    _ => unreachable!()
                }
            }
            if i <= n {
                curr_n_x.checked_sub_const_assign(powers_4[i]);
            }
            n_x.push(curr_n_x);
            n_D.push(curr_n_D);
        }

        // rules count

        // count the w's
        assert!(powers_4.len() >= n_x.len());
        for (pow, curr_n_x, curr_n_D) in izip!(&powers_4, n_x, n_D) {
            *n_counts.entry(0).or_default() += curr_n_x * pow; // N_X_LEFT
            *n_counts.entry(3).or_default() += curr_n_x * pow; // N_X_RIGHT

            *counts.entry(4).or_default() += curr_n_D as u128 * pow; // N_D_RIGHT
            *counts.entry(1).or_default() += curr_n_D as u128 * pow; // N_D_LEFT
        }

        // count number of times the head goes off to the right
        *counts.entry(5).or_default() += powers_4[n+1];   // right stride
        
        // count the C's
        let a1 = powers_4[n+1] - 1;
        let a2 = a1 / 3;
        let p16 = 1u128.checked_shl(4 * (n as u32 + 1)).unwrap();
        let rep_x_both = ((p16 - 1) / 15 - a2) * 9 / 2;
        let rep_x_left = a2 * 4;
        (*n_counts.entry(0).or_default()).checked_add_const_assign(rep_x_both + rep_x_left); // N_X_LEFT
        (*n_counts.entry(3).or_default()).checked_add_const_assign(rep_x_both + a1); // N_X_RIGHT

        for type_id in [8, 9, 10, 2, 7] { // N_C0_LEFT, N_C1_LEFT, N_C2_LEFT, N_C_LEFT, N_C_RIGHT
            *counts.entry(type_id).or_default() += a2;
        }
    }
}

fn to_sorted_pairs<T>(map: &HashMap<usize, T>) -> Vec<(usize, T)> 
where T: Clone
{
    let mut v: Vec<(usize, T)> = map.iter().map(|(a, b)| (*a, b.clone())).collect();
    v.sort_by_key(|x| x.0);
    v
}

fn add_counts<'a, T>(a: &'a HashMap<usize, T>, b: &'a HashMap<usize, T>) -> HashMap<usize, T>
where T: 'a + AddAssign<&'a T> + Default
{
    let mut out = HashMap::new();

    for counts in [a, b] {
        for (id, count) in counts {
            *out.entry(*id).or_default() += count;
        }
    }

    out
}

/// Write the @uni-cycle rule as
///    J x^(n+P) C1 D >       r   -->
///  F J x^n     C1 D > G s^T(r)
/// The x^(n+P) block of the @uni-cycle rule gradually becomes x^n, while the head passes through it a bunch of times.
/// Try to count the steps due to x^n and the steps due to the other x's.
/// 
/// I also let N1 = n + P, N0 = n.
/// 
/// Here, I try to count the number of times the counter rules are applied over the course of one uni-cycle.
/// Due to the x^n block, some rule counts need to be generic over the size of the x^n block.
/// I use the Binomial struct to count those.
/// I think of a Binomial instance as a0 + a1 * N.  Here N refers to N0.
pub fn measure_uni_cycle(do_print: bool, N0: u128, nr1: u128) {
    use CounterSymbol::*;
    use CounterBlockType::*;
    use CounterStepInfo::*;

    const P: u128 = 53946;
    let N1: u128 = N0 + P;
    let mut ltape = vec![L];
    ltape.extend_from_slice(left_block_definition()[&J].as_slice());
    ltape.extend(vec![X(N1), C1, D]);

    let mut rtape = vec![X(nr1), D, X(1000000), C, X(1000000), R];
    let r_xnr_idx = rtape.len() - 1;
    rtape.reverse();

    let mut sim = CounterSimulator {
        left_tape: ltape,
        right_tape: rtape,
        dir: Direction::Right,
        base_steps: 0,
        rle_steps: 0,
        do_strides: true,
        do_uni_cycles: false,
        self_steps: 0
    };

    let mut stride_times: Vec<_> = Vec::new();
    let mut stride_levels: Vec<usize> = Vec::new();
    let mut stride_rtapes: Vec<Vec<CounterSymbol>> = Vec::new();
    let mut n_strides_right: usize = 0;
    let mut rule_count: HashMap<usize, u128> = HashMap::new();
    let mut exp_rules: Vec<CounterStepInfo> = Vec::new();

    let mut exp_total: HashMap<usize, Binomial> = HashMap::new();

    let mut stride_counter_rule_counts: HashMap<usize, u128> = HashMap::new();
    let mut stride_counter_rule_n_counts: HashMap<usize, Binomial> = HashMap::new();

    let mut r_strides_step_count_prediction: Option<NSteps> = None;

    for i in 0..4000 {
        let mut sim_r = sim.clone();
        sim_r.rewrite_with_blocks(&vec![J], &vec![]);
        if do_print {
            println!("{}", sim_r);
        }

        if sim_r.left_tape.contains(&Block(J, 1)) &&
            sim_r.dir == Direction::Right &&
            sim_r.left_tape.ends_with(&[C1, D])
        {
            sim_r.rewrite_with_blocks(&vec![LeftDebris, A, G], &vec![G]);
            println!("{}", sim_r);

            for &level in &stride_levels {
                assert!(level >= 1);
                n_strides_right += 4usize.pow(level as u32 - 1);
            }

            if i == 0 {
                let mut sim2 = sim.clone();
                r_strides_step_count_prediction = Some(sim2.multi_stride(215779).unwrap().1);
            }

            if i > 0 {
                // println!("strides: {} {:?} ({}, {})", n_strides_right, stride_levels, stride_levels.len(), stride_rtapes.len());
                n_strides_right = 0;

                // println!("right tapes before applications of stride rule:");
                // for (idx, rtape) in stride_rtapes.iter().enumerate() {
                //     print!("{}/{}: ", idx+1, stride_rtapes.len());
                //     for symb in rtape {
                //         print!("{} ", symb);
                //     }
                //     println!();
                // }
                
                // print!("rule count: ");
                // for (id, count) in to_sorted_pairs(&rule_count) {
                //     print!("S{}: {}, ", id, count);
                // }
                // println!();

                // print!("N rule count: ");
                // for (id, count) in to_sorted_pairs(&exp_total) {
                //     print!("S{}: {}, ", id, count);
                // }
                // println!();

                // print!("stride rule count: ");
                // for (id, count) in to_sorted_pairs(&stride_counter_rule_counts) {
                //     if id == 5 {
                //         print!("(right stride): {}, ", count);
                //     } else {
                //         print!("S{}: {}, ", id, count);
                //     }
                // }
                // println!();

                // print!("stride rule N count: ");
                // for (id, count) in to_sorted_pairs(&stride_counter_rule_n_counts) {
                //     print!("S{}: {}, ", id, count);
                // }
                // println!();

                println!("predicted steps:");
                println!("{:?}", N_SINGLE_UNICYCLE_CONST + N_SINGLE_UNICYCLE_N * N0 + r_strides_step_count_prediction.clone().unwrap());

                let total_counts_normal = add_counts(&rule_count, &stride_counter_rule_counts);
                let total_counts_N = add_counts(&exp_total, &stride_counter_rule_n_counts);
                print!("totals (normal): ");
                for (id, count) in to_sorted_pairs(&total_counts_normal) {
                    if id == 5 {
                        print!("(right stride): {}, ", count);
                    } else {
                        print!("S{}: {}, ", id, count);
                    }
                }
                println!();

                print!("totals (N): ");
                for (id, count) in to_sorted_pairs(&total_counts_N) {
                    print!("S{}: {}, ", id, count);
                }
                println!();

                // println!("{:?}", exp_rules);
            }

            if sim.self_steps > 0 {
                return;
            }

            stride_rtapes.clear();
            stride_levels.clear();
            rule_count.clear();
            exp_rules.clear();
            exp_total.clear();

            // I don't have a good way to reset the stride counter rule counting yet
            // would need to update N0, N1, and r_xnr_idx in addition to clearing these two hashmaps
            stride_counter_rule_counts.clear();
            stride_counter_rule_n_counts.clear();
        }

        if sim.can_do_stride() {
            stride_rtapes.push(sim.right_tape.clone());
            measure_partial_stride(&mut stride_counter_rule_counts, &mut stride_counter_rule_n_counts,
                &sim.right_tape, r_xnr_idx, N0, N1);
        }

        match sim.step().unwrap() {
            Stride { level} => {
                stride_times.push(sim.self_steps);
                stride_levels.push(level);
            },
            S(id) => {
                *rule_count.entry(id).or_default() += 1;
            },
            r @ _ => {
                exp_rules.push(r);
                let (type_id, exp) = match r {
                    S0(n) => (0, n),
                    S3(n) => (3, n),
                    S23(n) => (23, n),
                    _ => unreachable!()
                };

                *exp_total.entry(type_id).or_default() += n_infer(exp, N0, N1);
            },
        }
        assert_eq!(sim.right_tape.get(r_xnr_idx), Some(&X(nr1)));
    }
}

fn n_infer(exp: u128, N0: u128, N1: u128) -> Binomial {
    if exp < N0 {
        Binomial { a0: exp, a1: 0 }
    } else if N0 <= exp && exp <= N1 {
        Binomial { a0: exp-N0, a1: 1 }
    } else {
        unreachable!()
    }
}

#[test]
fn replace_J() {
    use CounterSymbol::*;
    use CounterBlockType::*;

    let mut sim = CounterSimulator::new(true, true);
    sim.left_tape.extend_from_slice(&left_block_definition()[&J]);
    sim.left_tape.pop();
    sim.right_tape.push(C1); // to prevent it from doing a stride
    sim.right_tape.push(D);

    sim.step().unwrap();

    assert_eq!(sim.left_tape, [L, C1, Block(J, 1)]);
    assert_eq!(sim.right_tape, [R, C1]);
}