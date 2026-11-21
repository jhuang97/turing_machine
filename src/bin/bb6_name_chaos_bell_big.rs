use dashu_int::{
    UBig, Word,
    ops::{BitTest, PowerOfTwo},
};
use dashu_macros::ubig;
use num_order::NumOrd;
use std::fmt;
use strum_macros::EnumString;

const TM_DEF: &str = "1RB1RF_1LC1LB_1RD1LD_1RE0RA_---0LB_0LF0RC";

#[derive(Debug, Clone, PartialEq)]
pub enum SimError {
    Halted,
    UndefinedTransition,
}

impl fmt::Display for SimError {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Self::Halted => write!(f, "Halted"),
            Self::UndefinedTransition => write!(f, "Undefined transition"),
        }
    }
}

#[derive(PartialEq, Eq, Clone, Copy)]
enum HigherState {
    Left,
    LeftWide,
    LeftChange,
    Right,
}

#[derive(Debug, Default, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
enum RunSymbolType {
    #[default]
    U,
    V,
    X,
    Y,
    J,
    F,
}

#[derive(Debug, Default, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
enum SingleSymbolType {
    #[default]
    L,
    T,
    R,
    R0,
    Q,
    W,
    K,
    S,
}

#[derive(Debug, PartialEq, EnumString, Clone, Eq, Hash)]
enum BlockSymbol {
    Run(RunSymbolType, UBig),
    Single(SingleSymbolType),
}

fn add_or_merge_run(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType, nadd: UBig) {
    use BlockSymbol::*;
    match tape.last_mut() {
        Some(Run(t, n)) if *t == run_type => *n += nadd,
        _ => tape.push(Run(run_type, nadd)),
    }
}

fn decrement_run(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType) {
    use BlockSymbol::*;
    match tape.last_mut() {
        Some(Run(t, n)) if *t == run_type && *n == UBig::ONE => {
            tape.pop();
        }
        Some(Run(t, n)) if *t == run_type && *n > UBig::ONE => *n -= 1u8,
        _ => unreachable!("expected at least one of run symbol"),
    }
}

fn decrease_run_by(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType, nsub: UBig) {
    use BlockSymbol::*;
    match tape.last_mut() {
        Some(Run(t, n)) if *t == run_type && *n == nsub => {
            tape.pop();
        }
        Some(Run(t, n)) if *t == run_type && *n > nsub => *n -= nsub,
        _ => unreachable!("expected at least {} of run symbol", nsub),
    }
}

const ONE: UBig = UBig::ONE;

impl BlockSimulator {
    fn basic_step(&mut self) -> Result<UBig, SimError> {
        use BlockSymbol::Run;
        use BlockSymbol::Single as Si;
        use HigherState::*;
        use RunSymbolType::*;
        use SingleSymbolType::*;

        let n_steps = match (
            &self.state,
            self.left_tape.as_slice(),
            self.right_tape.as_slice(),
        ) {
            // < F F F Q -> < Y (1/2)
            // > F F F Q -> > Y (1/2)
            (Left | Right, _, [.., Si(Q), Run(F, n)]) if n.num_eq(&3u8) => {
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
                ubig!(0)
            }
            // < J Y F Q -> < J J
            // <c J Y F Q -> <c J J
            (Left | LeftChange, _, [.., Si(Q), Run(F, n0), Run(Y, n1), Run(J, n2)])
                if *n0 == ONE && *n1 == ONE && *n2 == ONE =>
            {
                self.right_tape.pop();
                self.right_tape.pop();
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, J, ubig!(2));
                ubig!(0)
            }
            // > X -> U >
            (Right, _, [.., Run(X, _)]) => {
                let Some(Run(X, n)) = self.right_tape.pop() else {
                    unreachable!()
                };
                add_or_merge_run(&mut self.left_tape, U, n.clone());
                5u128 * n
            }
            // > Y -> V V >
            (Right, _, [.., Run(Y, _)]) => {
                decrement_run(&mut self.right_tape, Y);
                add_or_merge_run(&mut self.left_tape, V, ubig!(2));
                ubig!(4)
            }
            // U < -> < X
            (Left, [.., Run(U, _)], _) => {
                let Some(Run(U, n)) = self.left_tape.pop() else {
                    unreachable!()
                };
                add_or_merge_run(&mut self.right_tape, X, n.clone());
                5u128 * n
            }
            // V V < -> < Y (handle elsewhere)
            // > R -> V < R
            (Right, _, [.., Si(R)]) => {
                self.state = Left;
                add_or_merge_run(&mut self.left_tape, V, ubig!(1));
                ubig!(4)
            }
            // L < -> L > X
            (Left, [.., Si(L)], _) => {
                self.state = Right;
                add_or_merge_run(&mut self.right_tape, X, ubig!(1));
                ubig!(5)
            }
            // L V < -> L > Y
            (Left, [.., Si(L), Run(V, n)], _) if *n == ONE => {
                self.state = Right;
                self.left_tape.pop();
                add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
                ubig!(6)
            }
            // L T < Y -> L > J
            (Left, [.., Si(L), Si(T)], [.., Run(Y, _)]) => {
                self.state = Right;
                self.left_tape.pop();
                decrement_run(&mut self.right_tape, Y);
                add_or_merge_run(&mut self.right_tape, J, ubig!(1));
                ubig!(10)
            }
            // U V < -> T > Y
            (Left, [.., Run(U, _), Run(V, n)], _) if *n == ONE => {
                self.state = Right;
                self.left_tape.pop();
                decrement_run(&mut self.left_tape, U);
                self.left_tape.push(Si(T));
                add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
                ubig!(6)
            }
            // L T V < -> L > X Y Q
            (Left, [.., Si(L), Si(T), Run(V, n)], _) if *n == ONE => {
                self.state = Right;
                self.left_tape.pop();
                self.left_tape.pop();
                self.right_tape.push(Si(Q));
                self.right_tape.push(Run(Y, ubig!(1)));
                self.right_tape.push(Run(X, ubig!(1)));
                ubig!(22)
            }
            // V T V < -> < W
            (Left, [.., Run(V, _), Si(T), Run(V, n)], _) if *n == ONE => {
                self.left_tape.pop();
                self.left_tape.pop();
                decrement_run(&mut self.left_tape, V);
                self.right_tape.push(Si(W));
                ubig!(7)
            }
            // U U T V < Y -> < Y Y W (1/2)
            (Left, [.., Run(U, n2), Si(T), Run(V, n1)], [.., Run(Y, _)])
                if n2.num_ge(&2u8) && *n1 == ONE =>
            {
                self.left_tape.pop();
                self.left_tape.pop();
                decrease_run_by(&mut self.left_tape, U, ubig!(2));
                decrement_run(&mut self.right_tape, Y);
                self.right_tape.push(Si(W));
                self.right_tape.push(Run(Y, ubig!(2)));
                ubig!(47)
            }
            // T < Y Y -> <w F F Q (1/2)
            (Left, [.., Si(T)], [.., Run(Y, n)]) if n.num_ge(&2u8) => {
                self.state = LeftWide;
                self.left_tape.pop();
                decrease_run_by(&mut self.right_tape, Y, ubig!(2));
                self.right_tape.push(Si(Q));
                self.right_tape.push(Run(F, ubig!(2)));
                ubig!(9)
            }
            // V <w -> <w F F (elsewhere)
            // T <w F -> < J F F
            (LeftWide, [.., Si(T)], [.., Run(F, _)]) => {
                self.state = Left;
                self.left_tape.pop();
                decrement_run(&mut self.right_tape, F);
                add_or_merge_run(&mut self.right_tape, F, ubig!(2));
                self.right_tape.push(Run(J, ubig!(1)));
                ubig!(1)
            }
            // U U <w F F Q -> <c J (1/4)
            (LeftWide, [.., Run(U, n1)], [.., Si(Q), Run(F, n2)])
                if n1.num_ge(&2u8) && n2.num_eq(&2u8) =>
            {
                self.state = LeftChange;
                decrease_run_by(&mut self.left_tape, U, ubig!(2));
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, J, ubig!(1));
                ubig!(62)
            }
            // U U <w F -> <c Y (1/2)
            (LeftWide, [.., Run(U, n)], [.., Run(F, _)]) if n.num_ge(&2u8) => {
                self.state = LeftChange;
                decrease_run_by(&mut self.left_tape, U, ubig!(2));
                decrement_run(&mut self.right_tape, F);
                add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
                ubig!(62)
            }
            // U U <c -> <c J (elsewhere)
            // L U <c -> L V > J Y
            (LeftChange, [.., Si(L), Run(U, n)], _) if *n == ONE => {
                self.state = Right;
                self.left_tape.pop();
                self.left_tape.push(Run(V, ubig!(1)));
                add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
                self.right_tape.push(Run(J, ubig!(1)));
                ubig!(1)
            }
            // L <c -> L > J Y
            (LeftChange, [.., Si(L)], _) => {
                self.state = Right;
                add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
                self.right_tape.push(Run(J, ubig!(1)));
                ubig!(1)
            }
            // > W -> < Y Q
            (Right, _, [.., Si(W)]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.push(Si(Q));
                self.right_tape.push(Run(Y, ubig!(1)));
                ubig!(10)
            }
            // > K -> < J
            (Right, _, [.., Si(K)]) => {
                self.state = Left;
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, J, ubig!(1));
                ubig!(10)
            }
            // > J Y -> < Y K
            (Right, _, [.., Run(Y, _), Run(J, n)]) if *n == ONE => {
                self.state = Left;
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Y);
                self.right_tape.push(Si(K));
                self.right_tape.push(Run(Y, ubig!(1)));
                ubig!(16)
            }
            // > J X -> < Y W
            (Right, _, [.., Run(X, _), Run(J, n)]) if *n == ONE => {
                self.state = Left;
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, X);
                self.right_tape.push(Si(W));
                self.right_tape.push(Run(Y, ubig!(1)));
                ubig!(16)
            }
            // > J J -> < Y K S (1/2)
            (Right, _, [.., Run(J, n)]) if n.num_ge(&2u8) => {
                self.state = Left;
                decrease_run_by(&mut self.right_tape, J, ubig!(2));
                self.right_tape.push(Si(S));
                self.right_tape.push(Si(K));
                self.right_tape.push(Run(Y, ubig!(1)));
                ubig!(16)
            }
            // > J F -> V V < F F F
            (Right, _, [.., Run(F, _), Run(J, n)]) if *n == ONE => {
                self.state = Left;
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, F);
                add_or_merge_run(&mut self.left_tape, V, ubig!(2));
                add_or_merge_run(&mut self.right_tape, F, ubig!(3));
                ubig!(10)
            }
            // > J S -> V V < Y
            (Right, _, [.., Si(S), Run(J, n)]) if *n == ONE => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, V, ubig!(2));
                add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
                ubig!(10)
            }
            // > J Q Y -> V V V < W
            (Right, _, [.., Run(Y, _), Si(Q), Run(J, n)]) if *n == ONE => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Y);
                add_or_merge_run(&mut self.left_tape, V, ubig!(3));
                self.right_tape.push(Si(W));
                ubig!(8)
            }
            // > J Q W -> V V V < K
            // later
            // > J R -> < Y Y R0
            // later
            // U > Q Y -> T V V U >
            (Right, [.., Run(U, _)], [.., Run(Y, _), Si(Q)]) => {
                decrement_run(&mut self.left_tape, U);
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Y);
                self.left_tape.push(Si(T));
                self.left_tape.push(Run(V, ubig!(2)));
                self.left_tape.push(Run(U, ubig!(1)));
                ubig!(15)
            }
            // V > Q Y -> < Y X
            (Right, [.., Run(V, _)], [.., Run(Y, _), Si(Q)]) => {
                self.state = Left;
                decrement_run(&mut self.left_tape, V);
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Y);
                add_or_merge_run(&mut self.right_tape, X, ubig!(1));
                self.right_tape.push(Run(Y, ubig!(1)));
                ubig!(6)
            }
            // V > Q W -> < Y Y
            (Right, [.., Run(V, _)], [.., Si(W), Si(Q)]) => {
                self.state = Left;
                decrement_run(&mut self.left_tape, V);
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, Y, ubig!(2));
                ubig!(6)
            }
            // > F F F F -> V V < (1/2)
            (Right, _, [.., Run(F, n)]) if n.num_ge(&4u8) => {
                self.state = Left;
                decrease_run_by(&mut self.right_tape, F, ubig!(4));
                add_or_merge_run(&mut self.left_tape, V, ubig!(2));
                ubig!(4)
            }
            // > F Q Y -> < K
            (Right, _, [.., Run(Y, _), Si(Q), Run(F, n)]) if *n == ONE => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Y);
                self.right_tape.push(Si(K));
                ubig!(6)
            }
            _ => return Err(SimError::UndefinedTransition),
        };

        Ok(n_steps)
    }
}

impl fmt::Display for BlockSimulator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        const LEFT_PRINT_THRESHOLD: usize = 100;
        let l_th = LEFT_PRINT_THRESHOLD / 2;
        self.self_steps.fmt(f)?;
        write!(f, " | {}: ", ShortenedHex(&self.base_steps))?;
        if self.left_tape.len() <= LEFT_PRINT_THRESHOLD {
            for symb in &self.left_tape {
                write!(f, "{} ", symb)?;
            }
        } else {
            for symb in &self.left_tape[..l_th] {
                write!(f, "{} ", symb)?;
            }
            write!(
                f,
                " ...{} terms... ",
                self.left_tape.len() - LEFT_PRINT_THRESHOLD
            )?;
            for symb in &self.left_tape[self.left_tape.len() - l_th..] {
                write!(f, "{} ", symb)?;
            }
        }
        match self.state {
            HigherState::Left => write!(f, "{}", "<".red().bold())?,
            HigherState::LeftWide => write!(f, "{}", "<w".red().bold())?,
            HigherState::LeftChange => write!(f, "{}", "<c".red().bold())?,
            HigherState::Right => write!(f, "{}", ">".red().bold())?,
        }
        const RIGHT_PRINT_THRESHOLD: usize = 200;
        let r_th = RIGHT_PRINT_THRESHOLD / 2;
        if self.right_tape.len() <= RIGHT_PRINT_THRESHOLD {
            for symb in self.right_tape.iter().rev() {
                write!(f, " {}", symb)?;
            }
        } else {
            for symb in self.right_tape[self.right_tape.len() - r_th..].iter().rev() {
                write!(f, " {}", symb)?;
            }
            write!(
                f,
                " ...{} terms... ",
                self.right_tape.len() - RIGHT_PRINT_THRESHOLD
            )?;
            for symb in self.right_tape[..r_th].iter().rev() {
                write!(f, " {}", symb)?;
            }
        }
        Ok(())
    }
}

struct BlockSimulator {
    pub left_tape: Vec<BlockSymbol>,
    pub right_tape: Vec<BlockSymbol>,
    pub state: HigherState,
    pub base_steps: UBig,
    pub self_steps: u64,
    pub accelerate_bells: bool,
}

impl fmt::Display for BlockSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use BlockSymbol::*;
        let s0 = match *self {
            Run(t, _) => &format!("{:?}", t),
            Single(t) => &format!("{:?}", t),
        };
        let s_exp = match self {
            Run(_, n) => {
                if *n == UBig::ONE {
                    ""
                } else {
                    &format!("^{}", ShortenedHex(n))
                }
            }
            _ => "",
        };
        write!(f, "{}{}", s0, s_exp)
    }
}

impl BlockSimulator {
    fn new(accelerate_bells: bool) -> Self {
        use BlockSymbol::*;
        use SingleSymbolType::*;
        Self {
            left_tape: vec![Single(L)],
            right_tape: vec![Single(R)],
            state: HigherState::Left,
            base_steps: ubig!(3),
            self_steps: 0,
            accelerate_bells,
        }
    }

    fn bell_step(&mut self) -> Option<Result<UBig, SimError>> {
        use BlockSymbol::{Run, Single as Si};
        use HigherState::*;
        use RunSymbolType::*;
        use SingleSymbolType::*;

        if self.state != Right {
            return None;
        }

        let u_k = match self.left_tape.as_slice() {
            [Si(L)] => UBig::ZERO,
            [Si(L), Run(U, n)] => n.clone(),
            _ => return None,
        };

        let mut right_sl = self.right_tape.as_slice();
        let y_k = match right_sl {
            [rest @ .., Run(Y, n)] => {
                let k = n.clone();
                right_sl = rest;
                k
            }
            _ => UBig::ZERO,
        };

        let (n_heads, right_steps, y_k_new) = match right_sl {
            // y^3n Y^k J^2n -> Y^k+3n
            [.., Run(J, m)] if m.num_ge(&2u8) => {
                let n = m / 2u8;
                if y_k > UBig::ZERO {
                    self.right_tape.pop();
                }
                decrease_run_by(&mut self.right_tape, J, 2u8 * &n);
                // n(30k + 45n + 17)
                let s = &n * (30u8 * &y_k + 45u8 * &n + 17u8);
                let n3 = n * 3u8;
                let y_k_new = y_k + &n3;
                (n3, s, y_k_new)
            }
            // y^n Y^k F^4n -> Y^k+n
            [.., Run(F, m)] if m.num_ge(&4u8) => {
                let n = m / 4u8;
                if y_k > UBig::ZERO {
                    self.right_tape.pop();
                }
                decrease_run_by(&mut self.right_tape, F, 4u8 * &n);
                // 5 * n * (2 * y_k + n + 1)
                let s = (&y_k * 2u8 + &n + 1u8) * &n * 5u8;
                let y_k_new = y_k + &n;
                (n, s, y_k_new)
            }
            // y^2n Y^k J Y^n -> Y^k+n J
            [.., Run(Y, n0), Run(J, n1)] if *n0 >= ONE && *n1 == ONE => {
                let n = n0.clone();
                if y_k > UBig::ZERO {
                    self.right_tape.pop();
                }
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, J, ubig!(1));
                // n * ((y_k * 2 + n) * 10 + 26)
                let s = ((&y_k * 2u8 + &n) * 10u8 + 26u8) * &n;
                (2u8 * &n, s, y_k + n)
            }
            _ => return None,
        };
        add_or_merge_run(&mut self.right_tape, Y, y_k_new);

        let left_steps = (u_k * 2u8 + &n_heads + 1u8) * &n_heads * 5u8;
        add_or_merge_run(&mut self.left_tape, U, n_heads);

        Some(Ok(left_steps + right_steps))
    }

    fn multi_shift_step(&mut self) -> Option<Result<UBig, SimError>> {
        use BlockSymbol::{Run, Single as Si};
        use HigherState::*;
        use RunSymbolType::*;
        use SingleSymbolType::*;
        let n_steps = match (
            &self.state,
            self.left_tape.as_slice(),
            self.right_tape.as_slice(),
        ) {
            // > Y -> V V >
            (Right, _, [.., Run(Y, _)]) => {
                let Some(Run(Y, n)) = self.right_tape.pop() else {
                    unreachable!()
                };
                add_or_merge_run(&mut self.left_tape, V, 2u128 * n.clone());
                4u128 * n
            }
            // V V < -> < Y
            (Left, [.., Run(V, m)], _) if m.num_ge(&2u8) => {
                let n = m / &2u8;
                decrease_run_by(&mut self.left_tape, V, 2u128 * &n);
                add_or_merge_run(&mut self.right_tape, Y, n.clone());
                6u128 * n
            }
            // U U <c -> <c J (1/2)
            (LeftChange, [.., Run(U, m)], _) if m.num_ge(&2u8) => {
                let n = m / &2u8;
                decrease_run_by(&mut self.left_tape, U, 2u128 * &n);
                add_or_merge_run(&mut self.right_tape, J, n.clone());
                62u128 * n
            }
            // V <w -> <w F F
            (LeftWide, [.., Run(V, _)], _) => {
                let Some(Run(V, n)) = self.left_tape.pop() else {
                    unreachable!()
                };
                add_or_merge_run(&mut self.right_tape, F, 2u128 * &n);
                26u128 * n
            }
            _ => return None,
        };
        Some(Ok(n_steps))
    }

    fn step(&mut self) -> Result<(), SimError> {
        use BlockSymbol::{Run, Single as Si};
        use HigherState::*;
        use RunSymbolType::*;
        use SingleSymbolType::*;

        let new_base_steps = if matches!(
            (&self.state, self.right_tape.as_slice(),),
            (Left | Right, [.., Si(Q), Run(F, _)])
        ) && let Some(Run(F, n)) = self.right_tape.last()
            && n.num_eq(&3u8)
        {
            // < F F F Q -> < Y
            self.right_tape.pop();
            self.right_tape.pop();
            add_or_merge_run(&mut self.right_tape, Y, ubig!(1));
            UBig::ZERO
        } else if matches!(&self.state, Left | LeftChange)
            && let [.., Si(Q), Run(F, n0), Run(Y, n1), Run(J, n2)] = self.right_tape.as_slice()
            && *n0 == ONE
            && *n1 == ONE
            && *n2 == ONE
        {
            // < J Y F Q -> < J J
            // <c J Y F Q -> <c J J
            self.right_tape.pop();
            self.right_tape.pop();
            self.right_tape.pop();
            self.right_tape.pop();
            add_or_merge_run(&mut self.right_tape, J, ubig!(2));
            UBig::ZERO
        } else if self.accelerate_bells
            && let Some(res) = self.bell_step()
        {
            res?
        } else if let Some(res) = self.multi_shift_step() {
            res?
        } else {
            self.basic_step()?
        };
        self.base_steps += new_base_steps;
        self.self_steps += 1;
        Ok(())
    }
}

struct ShortenedHex<'a>(&'a UBig);

impl<'a> fmt::Display for ShortenedHex<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        const LIMIT: u128 = u128::MAX;
        if self.0.num_le(&LIMIT) {
            write!(f, "{}", self.0)
        } else {
            let w = self.0.as_words();
            assert!(w.len() > 1);
            let w_l1 = w[w.len() - 1];
            let l1_n_bits = w_l1.ilog2() + 1;
            let l1_n_hex = l1_n_bits.div_ceil(4);
            // println!("l1_n_hex {l1_n_hex}");
            let left = if l1_n_hex >= 8 {
                w_l1 >> (4 * (l1_n_hex - 8))
            } else {
                let l2_n_hex = 8 - l1_n_hex;
                let w_l2 = w[w.len() - 2];
                (w_l1 << (4 * l2_n_hex)) + (w_l2 >> (Word::BITS - 4 * l2_n_hex))
            };
            let right = w[0] % (1 << 32);
            write!(f, "0x{left:x}..{right:08x}")?;
            if self.0.is_power_of_two() {
                write!(f, "(=2^{})", self.0.bit_len() - 1)
            } else {
                write!(f, "(>2^{})", self.0.bit_len() - 1)
            }
        }
    }
}

fn try_print_ubig(n: &UBig) {
    println!("hex: {:#x}, decimal: {}", n, n);
    println!("{}", ShortenedHex(n));
}

fn _figuring_out_how_to_format_ubig() {
    {
        struct S(UBig);
        let n = S(ubig!(12345));

        match &n {
            S(x) if x.num_eq(&1245) => println!("matched"),
            _ => println!("not matched"),
        }

        match &n {
            S(x) if x.num_lt(&12346) => println!("matched"),
            _ => println!("not matched"),
        }

        println!("{}", n.0);
    }

    println!("{}", u64::MAX);
    println!("{}", u128::MAX);

    let n = ubig!(123412342342345345674657576823454533456453456);
    let w = n.as_words();
    println!("{:?}", Word::BITS);
    println!("{} bits", n.bit_len());

    println!("0x12345678..12345678(> 2^123)");

    if n.is_power_of_two() {
        println!("= 2^{}", n.bit_len() - 1);
    } else {
        println!("> 2^{}", n.bit_len() - 1);
    }

    println!("{:#x}", n);

    println!("{:x}..{:x}, {} words", w[w.len() - 1], w[0], w.len());
    println!("{:#?}", n);

    for n in [
        ubig!(2),
        ubig!(1000),
        ubig!(1048576),
        ubig!(340282366920938463463374607431768211455),
        ubig!(340282366920938463463374607431768211456),
        ubig!(340282366920938463463374607431768211457),
        ubig!(680564733841876926926749214863536422911),
        ubig!(680564733841876926926749214863536422912),
        ubig!(680564733841876926926749214863536422913),
        ubig!(21778071482940061661655974875633165533183),
        ubig!(21778071482940061661655974875633165533184),
        ubig!(21778071482940061661655974875633165533185),
        ubig!(43556142965880123323311949751266331066367),
        ubig!(43556142965880123323311949751266331066368),
        ubig!(43556142965880123323311949751266331066369),
        ubig!(34572948792498314098414091857163498091375309814091),
        ubig!(5019283740291354871239587210394871203948723098471209835),
        ubig!(719238473849213847912834791823473481729384739487294738479),
        ubig!(784637716923335095479473677900958302012794430558004314111),
        ubig!(784637716923335095479473677900958302012794430558004314112),
        ubig!(784637716923335095479473677900958302012794430558004314113),
        ubig!(210987215908175209865134095012958768510059182735498751209857),
        ubig!(3210987215908175209865134095012958769999059182735498751209857),
    ] {
        try_print_ubig(&n);
    }
}

fn main() {
    // _figuring_out_how_to_format_ubig();

    let mut sim = BlockSimulator::new(true);
    println!("{sim}");
    let max_steps = 3000;
    // let max_steps = 100000000;
    for k in 1..=max_steps {
        let res = sim.step();
        // if k % 100000 == 0 {
        println!("{sim}");
        // }
        if let Err(e) = res {
            println!("{sim} {e}");
            break;
        }
    }
}
