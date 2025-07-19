use strum_macros::EnumString;
use syn::TraitBoundModifier;
use core::panic;
use std::{collections::HashMap, fmt};
use auto_ops::impl_op_ex;

type Exp = u128;

#[derive(Debug, Clone)]
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

#[derive(PartialEq, Eq)]
enum HigherState {
    Left,
    Right,
    RightSlow,
}

#[derive(Debug, Default, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
enum RunSymbolType {
    #[default]
    X,
    Q,
    C,
    F,
}

#[derive(Debug, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
enum BlockSymbol {
    Run(RunSymbolType, Exp),
    L,
    R,
    Wildcard,
    P,
    D,
}

fn add_or_merge_run(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType, nadd: Exp) {
    use BlockSymbol::*;
    match tape.last_mut() {
        Some(Run(t, n)) if *t == run_type => *n += nadd,
        _ => tape.push(Run(run_type, nadd)),
    }
}
fn decrement_run(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType) {
    use BlockSymbol::*;
    match tape.last_mut() {
        Some(Run(t, 1)) if *t == run_type => {
            tape.pop();
        }
        Some(Run(t, n @ 2..)) if *t == run_type => *n -= 1,
        _ => unreachable!("expected at least one of run symbol"),
    }
}
fn decrease_run_by(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType, nsub: Exp) {
    use BlockSymbol::*;
    match tape.last_mut() {
        Some(Run(t, n)) if *t == run_type && *n == nsub => {
            tape.pop();
        }
        Some(Run(t, n)) if *t == run_type && *n > nsub => *n -= nsub,
        _ => unreachable!("expected at least {} of run symbol", nsub),
    }
}

/// a0 + a1 * N
#[derive(Default, Clone, Copy)]
pub struct Binomial {
    pub a0: Exp,
    pub a1: Exp
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

impl_op_ex!(+= |a: &mut Binomial, c: &Exp| {
    a.a0 += c;
});

impl_op_ex!(* |a: &Binomial, c: &Exp| -> Binomial {
    Binomial {
        a0: a.a0 * c,
        a1: a.a1 * c,
    }
});

impl_op_ex!(+= |a: &mut Binomial, b: &Binomial| {
    a.a0 += b.a0;
    a.a1 += b.a1;
});

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum RightwardState {
    Normal,
    P,
    Q,
    Slow
}

impl RightwardState {
    fn update(&self, state: &mut HigherState, rtape: &mut Vec<BlockSymbol>) {
        use RightwardState as RS;
        match &self {
            RS::Normal => *state = HigherState::Right,
            RS::P => {
                *state = HigherState::Right;
                (*rtape).push(BlockSymbol::P);
            },
            RS::Q => {
                *state = HigherState::Right;
                (*rtape).push(BlockSymbol::Run(RunSymbolType::Q, 1));
            },
            RS::Slow => *state = HigherState::RightSlow,
        }
    }
}

impl fmt::Display for RightwardState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use RightwardState as RS;
        match &self {
            RS::Normal => write!(f, ">"),
            RS::P => write!(f, ">P"),
            RS::Q => write!(f, ">Q"),
            RS::Slow => write!(f, "s>"),
        }
    }
}

#[derive(Clone, PartialEq, Eq, Hash)]
struct EncodedLTape(Vec<u16>);

impl EncodedLTape {
    fn decode(&self) ->  Vec<BlockSymbol> {
        self.0.iter().enumerate().map(|(i, exp)| {
            if i % 2 == 0 {
                BlockSymbol::Run(RunSymbolType::Q, *exp as Exp)
            } else {
                BlockSymbol::Run(RunSymbolType::X, *exp as Exp)
            }
        }).collect()
    }
}

// Maybe not the best way to organize things?
#[derive(Clone)]
struct PositionInfo {
    pos_new: EncodedLTape,
    nadd: Exp,
    steps: Binomial,
    rstate: RightwardState,
}

struct BlockInfo {
    ltape: Vec<BlockSymbol>,
    nadd: Exp,
    steps: Binomial,
    rstate: RightwardState,
}

impl fmt::Display for BlockInfo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} | n += {} | ", self.steps, self.nadd)?;
        for b in &self.ltape {
            write!(f, "{} ", b)?;
        }
        write!(f, "{}", self.rstate)
    }
}

impl PositionInfo {
    fn decode(&self) -> BlockInfo {
        BlockInfo {
            ltape: self.pos_new.decode(),
            nadd: self.nadd,
            steps: self.steps,
            rstate: self.rstate,
        }
    }
}

impl fmt::Display for BlockSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use BlockSymbol::*;
        let s0 = match *self {
            Run(t, _) => &format!("{:?}", t),
            Wildcard => "*",
            _ => &format!("{:?}", self),
        };
        let s_exp = match *self {
            Run(_, n) => if n == 1 { "" } else { &format!("^{}", n) }
            _ => "",
        };
        write!(f, "{}{}", s0, s_exp)
    }
}

struct Memo {
    pub positions: HashMap<EncodedLTape, PositionInfo>,
    pub steps: u64,
}

impl Memo {
    pub fn new() -> Self {
        // L X^n < ---(6n + 1)--> L X^n >
        let lxn = (EncodedLTape(vec![]), PositionInfo {
            pos_new: EncodedLTape(vec![]),
            nadd: 0,
            steps: Binomial { a0: 1, a1: 6 },
            rstate: RightwardState::Normal
        });

        Self {
            positions: HashMap::from([lxn]),
            steps: 0,
        }
    }
}

struct OuterSimulator {
    pub left_tape: Vec<BlockSymbol>,
    pub right_tape: Vec<BlockSymbol>,
    pub state: HigherState,
    pub base_steps: u128,
    pub self_steps: u64,
    pub accelerator: Option<Memo>,
}

impl OuterSimulator {
    pub fn new(accelerate: bool) -> Self {
        use BlockSymbol::*;
        use RunSymbolType::*;

        Self {
            left_tape: vec![L, Run(X, 1)],
            right_tape: vec![R, Run(F, 1)],
            state: HigherState::RightSlow,
            base_steps: 17,
            self_steps: 0,
            accelerator: if accelerate { Some(Memo::new()) } else { None }
        }
    }

    fn basic_step(&mut self) -> Result<Exp, SimError> {
        use HigherState::*;
        use BlockSymbol::*;
        use RunSymbolType::*;
        let n_steps = match (
            &self.state,
            self.left_tape.as_slice(),
            self.right_tape.as_slice(),
        ) {
            // L < -> L >
            (Left, [.., L], _) => {
                self.state = Right;
                1u128
            }
            // X < -> < X
            (Left, [.., Run(X, exp)], _) => {
                let n = *exp;
                self.left_tape.pop();
                add_or_merge_run(&mut self.right_tape, X, n);
                2u128 * n
            }
            // Q < D -> < C Q
            (Left, [.., Run(Q, _)], [.., D]) => {
                decrement_run(&mut self.left_tape, Q);
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(Run(C, 1u128));
                1u128
            }
            // Q < C -> < F Q
            (Left, [.., Run(Q, _)], [.., Run(C, _)]) => {
                decrement_run(&mut self.left_tape, Q);
                decrement_run(&mut self.right_tape, C);
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(Run(F, 1u128));
                1u128
            }
            // Q < X -> < C P
            (Left, [.., Run(Q, _)], [.., Run(X, _)]) => {
                decrement_run(&mut self.left_tape, Q);
                decrement_run(&mut self.right_tape, X);
                self.right_tape.push(P);
                self.right_tape.push(Run(C, 1u128));
                1u128
            }
            // Q < F P -> < F F
            (Left, [.., Run(Q, _)], [.., P, Run(F, 1)]) => {
                decrement_run(&mut self.left_tape, Q);
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, F, 2u128);
                1u128
            }
            // Q < F -> < F P
            (Left, [.., Run(Q, _)], [.., Run(F, _)]) => {
                decrement_run(&mut self.left_tape, Q);
                decrement_run(&mut self.right_tape, F);
                self.right_tape.push(P);
                self.right_tape.push(Run(F, 1u128));
                1u128
            }
            // Q < P -> < F
            (Left, [.., Run(Q, _)], [.., P]) => {
                decrement_run(&mut self.left_tape, Q);
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, F, 1u128);
                1u128
            }
            // Q < -> < P
            (Left, [.., Run(Q, _)], _) => {
                decrement_run(&mut self.left_tape, Q);
                self.right_tape.push(P);
                1u128
            }
            // > X -> X >
            (Right, _, [.., Run(X, exp)]) => {
                let n = *exp;
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, X, n);
                4u128 * n
            }
            // > D -> X s>
            (Right, _, [.., D]) => {
                self.state = RightSlow;
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, X, 1u128);
                4u128
            }
            // > C P -> < D F
            (Right, _, [.., P, Run(C, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, F, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > C Q -> < D C
            (Right, _, [.., Run(Q, _), Run(C, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                add_or_merge_run(&mut self.right_tape, C, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > C -> < D P
            (Right, _, [.., Run(C, _)]) => {
                self.state = Left;
                decrement_run(&mut self.right_tape, C);
                self.right_tape.push(P);
                self.right_tape.push(D);
                6u128
            }
            // > F P -> < D X
            (Right, _, [.., P, Run(F, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, X, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > F Q -> < D D
            (Right, _, [.., Run(Q, _), Run(F, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                self.right_tape.push(D);
                self.right_tape.push(D);
                6u128
            }
            // > F -> < D Q
            (Right, _, [.., Run(F, _)]) => {
                self.state = Left;
                decrement_run(&mut self.right_tape, F);
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > Q F R -> X < D F R
            (Right, _, [.., R, Run(F, 1), Run(Q, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, X, 1u128);
                self.right_tape.push(D);
                12u128
            }
            // > P R -> < D F R
            (Right, _, [.., R, P]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.push(Run(F, 1u128));
                self.right_tape.push(D);
                8u128
            }
            // > Q R -> < Q F R
            (Right, _, [.., R, Run(Q, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.push(Run(F, 1u128));
                self.right_tape.push(Run(Q, 1u128));
                8u128
            }
            // s> R -> < P D F R
            (RightSlow, _, [.., R]) => {
                self.state = Left;
                self.right_tape.push(Run(F, 1u128));
                self.right_tape.push(D);
                self.right_tape.push(P);
                14u128
            }
            // > P X -> > C P
            (Right, _, [.., Run(X, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, X);
                self.right_tape.push(P);
                self.right_tape.push(Run(C, 1u128));
                0u128
            }
            // > P D -> < D C
            (Right, _, [.., D, P]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, C, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > P C -> > F Q
            (Right, _, [.., Run(C, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, C);
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(Run(F, 1u128));
                0u128
            }
            // > P F -> > F P
            (Right, _, [.., Run(F, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, F);
                self.right_tape.push(P);
                self.right_tape.push(Run(F, 1u128));
                0u128
            }
            // > P P -> > F
            (Right, _, [.., P, P]) => {
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, F, 1u128);
                0u128
            }
            // > P Q -> > C
            (Right, _, [.., Run(Q, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                add_or_merge_run(&mut self.right_tape, C, 1u128);
                0u128
            }
            // > Q X -> > D P
            (Right, _, [.., Run(X, _), Run(Q, 1)]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, X);
                self.right_tape.push(P);
                self.right_tape.push(D);
                0u128
            }
            // > Q D -> > D Q
            (Right, _, [.., D, Run(Q, 1)]) => {
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(D);
                0u128
            }
            // > Q C -> X > Q
            (Right, _, [.., Run(C, exp), Run(Q, 1)]) => {
                let n = *exp;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, Q, 1);
                add_or_merge_run(&mut self.left_tape, X, n);
                4u128 * n
            }
            // > Q F -> > X P
            (Right, _, [.., Run(F, _), Run(Q, 1)]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, F);
                self.right_tape.push(P);
                self.right_tape.push(Run(X, 1u128));
                0u128
            }
            // > Q P -> > X
            (Right, _, [.., P, Run(Q, 1)]) => {
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, X, 1u128);
                0u128
            }
            // > Q Q -> > D (1/2)
            (Right, _, [.., Run(Q, 2u128..)]) => {
                decrease_run_by(&mut self.right_tape, Q, 2u128);
                self.right_tape.push(D);
                0u128
            }
            // > Q Q -> > D (2/2)
            (Right, _, [.., Run(Q, _), Run(Q, 1)]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                self.right_tape.push(D);
                0u128
            }
            // s> X -> Q > P
            (RightSlow, _, [.., Run(X, _)]) => {
                self.state = Right;
                decrement_run(&mut self.right_tape, X);
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                self.right_tape.push(P);
                3u128
            }
            // s> D -> Q > Q
            (RightSlow, _, [.., D]) => {
                self.state = Right;
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                3u128
            }
            // s> C -> Q Q >
            (RightSlow, _, [.., Run(C, _)]) => {
                self.state = Right;
                decrement_run(&mut self.right_tape, C);
                add_or_merge_run(&mut self.left_tape, Q, 2u128);
                6u128
            }
            // s> F -> Q Q s>
            (RightSlow, _, [.., Run(F, _)]) => {
                decrement_run(&mut self.right_tape, F);
                add_or_merge_run(&mut self.left_tape, Q, 2u128);
                6u128
            }
            // s> P -> Q s>
            (RightSlow, _, [.., P]) => {
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                3u128
            }
            // s> Q -> Q >
            (RightSlow, _, [.., Run(Q, _)]) => {
                self.state = Right;
                decrement_run(&mut self.right_tape, Q);
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                3u128
            }
            _ => return Err(SimError::UndefinedTransition),
        };
        Ok(n_steps)
    }

    pub fn step(&mut self) -> Result<(), SimError> {
        use BlockSymbol::Run;
        if self.state == HigherState::Left && let Some(accel) = self.accelerator.as_mut() {
            let ltape_main = self.left_tape.split_off(2);
            let Some(Run(RunSymbolType::X, left_exp)) = self.left_tape.get_mut(1) else { panic!() };

            let left_encoded = EncodedLTape(ltape_main.iter().enumerate().map(
                |(i, block)| match block {
                    Run(RunSymbolType::Q, exp) => {
                        assert!(i % 2 == 0);
                        u16::try_from(*exp).unwrap()
                    }
                    Run(RunSymbolType::X, exp) => {
                        assert!(i % 2 == 1);
                        u16::try_from(*exp).unwrap()
                    }
                    _ => unreachable!()
                }
            ).collect());

            let BlockInfo {ltape: ltape_new,
                nadd, steps, rstate} = get_or_calculate(&left_encoded, accel);
            self.base_steps += steps.a0 + steps.a1 * *left_exp;
            *left_exp += nadd;

            self.left_tape.extend(ltape_new);
            rstate.update(&mut self.state, &mut self.right_tape);
        } else {
            let new_base_steps = self.basic_step()?;
            self.base_steps = self.base_steps.checked_add(new_base_steps.into()).unwrap();
        }

        self.self_steps += 1;
        Ok(())
    }
}

impl fmt::Display for OuterSimulator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use colored::*;
        const LEFT_PRINT_THRESHOLD: usize = 26; // 100
        let l_th = LEFT_PRINT_THRESHOLD / 2;
        self.self_steps.fmt(f)?;
        write!(f, " | {}: ", self.base_steps)?;
        if self.left_tape.len() <= LEFT_PRINT_THRESHOLD {
            for symb in &self.left_tape {
                write!(f, "{} ", symb)?;
            }
        } else {
            for symb in &self.left_tape[..l_th] {
                write!(f, "{} ", symb)?;
            }
            write!(f, " ...{} terms... ", self.left_tape.len() - LEFT_PRINT_THRESHOLD)?;
            for symb in &self.left_tape[self.left_tape.len() - l_th..] {
                write!(f, "{} ", symb)?;
            }
        }
        match self.state {
            HigherState::Left => write!(f, "{}", "<".red().bold())?,
            HigherState::Right => write!(f, "{}", ">".red().bold())?,
            HigherState::RightSlow => write!(f, "{}", "s>".red().bold())?,
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
                f, " ...{} terms... ", self.right_tape.len() - RIGHT_PRINT_THRESHOLD
            )?;
            for symb in self.right_tape[..r_th].iter().rev() {
                write!(f, " {}", symb)?;
            }
        }
        Ok(())
    }
}

struct InnerSimulator {
    left_tape: Vec<BlockSymbol>,
    right_tape: Vec<BlockSymbol>,
    state: HigherState,
    base_steps: Binomial,
    nadd: Exp,
}

impl InnerSimulator {
    fn new(position: &EncodedLTape) -> Self {
        Self {
            left_tape: position.decode(),
            right_tape: vec![BlockSymbol::Wildcard],
            state: HigherState::Left,
            base_steps: Binomial { a0: 0, a1: 0},
            nadd: 0,
        }
    }

    fn basic_step(&mut self) -> Option<RightwardState> {
        use HigherState::*;
        use BlockSymbol::*;
        use RunSymbolType::*;
        let n_steps = match (
            &self.state,
            self.left_tape.as_slice(),
            self.right_tape.as_slice(),
        ) {
            // L < -> L >
            // (Left, [.., L], _) => {
            //     self.state = Right;
            //     1u128
            // }
            // X < -> < X
            (Left, [.., Run(X, exp)], _) => {
                let n = *exp;
                self.left_tape.pop();
                add_or_merge_run(&mut self.right_tape, X, n);
                2u128 * n
            }
            // // Q < D -> < C Q
            // (Left, [.., Run(Q, _)], [.., D]) => {
            //     decrement_run(&mut self.left_tape, Q);
            //     self.right_tape.pop();
            //     add_or_merge_run(&mut self.right_tape, Q, 1u128);
            //     self.right_tape.push(Run(C, 1u128));
            //     1u128
            // }
            // // Q < C -> < F Q
            // (Left, [.., Run(Q, _)], [.., Run(C, _)]) => {
            //     decrement_run(&mut self.left_tape, Q);
            //     decrement_run(&mut self.right_tape, C);
            //     add_or_merge_run(&mut self.right_tape, Q, 1u128);
            //     self.right_tape.push(Run(F, 1u128));
            //     1u128
            // }
            // // Q < X -> < C P
            // (Left, [.., Run(Q, _)], [.., Run(X, _)]) => {
            //     decrement_run(&mut self.left_tape, Q);
            //     decrement_run(&mut self.right_tape, X);
            //     self.right_tape.push(P);
            //     self.right_tape.push(Run(C, 1u128));
            //     1u128
            // }
            // // Q < F P -> < F F
            // (Left, [.., Run(Q, _)], [.., P, Run(F, 1)]) => {
            //     decrement_run(&mut self.left_tape, Q);
            //     self.right_tape.pop();
            //     self.right_tape.pop();
            //     add_or_merge_run(&mut self.right_tape, F, 2u128);
            //     1u128
            // }
            // // Q < F -> < F P
            // (Left, [.., Run(Q, _)], [.., Run(F, _)]) => {
            //     decrement_run(&mut self.left_tape, Q);
            //     decrement_run(&mut self.right_tape, F);
            //     self.right_tape.push(P);
            //     self.right_tape.push(Run(F, 1u128));
            //     1u128
            // }
            // // Q < P -> < F
            // (Left, [.., Run(Q, _)], [.., P]) => {
            //     decrement_run(&mut self.left_tape, Q);
            //     self.right_tape.pop();
            //     add_or_merge_run(&mut self.right_tape, F, 1u128);
            //     1u128
            // }
            // Q < -> < P
            (Left, [.., Run(Q, _)], _) => {
                decrement_run(&mut self.left_tape, Q);
                self.right_tape.push(P);
                1u128
            }
            // > X -> X >
            (Right, _, [.., Run(X, exp)]) => {
                let n = *exp;
                self.right_tape.pop();
                if self.left_tape.is_empty() {
                    self.nadd += n;
                } else {
                    add_or_merge_run(&mut self.left_tape, X, n);
                }
                4u128 * n
            }
            // > D -> X s>
            (Right, _, [.., D]) => {
                self.state = RightSlow;
                self.right_tape.pop();
                if self.left_tape.is_empty() {
                    self.nadd += 1;
                } else {
                    add_or_merge_run(&mut self.left_tape, X, 1u128);
                }
                4u128
            }
            // > C P -> < D F
            (Right, _, [.., P, Run(C, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, F, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > C Q -> < D C
            (Right, _, [.., Run(Q, _), Run(C, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                add_or_merge_run(&mut self.right_tape, C, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > C -> < D P
            (Right, _, [.., Run(C, _)]) => {
                self.state = Left;
                decrement_run(&mut self.right_tape, C);
                self.right_tape.push(P);
                self.right_tape.push(D);
                6u128
            }
            // > F P -> < D X
            (Right, _, [.., P, Run(F, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, X, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > F Q -> < D D
            (Right, _, [.., Run(Q, _), Run(F, 1)]) => {
                self.state = Left;
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                self.right_tape.push(D);
                self.right_tape.push(D);
                6u128
            }
            // > F -> < D Q
            (Right, _, [.., Run(F, _)]) => {
                self.state = Left;
                decrement_run(&mut self.right_tape, F);
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // // > Q F R -> X < D F R
            // (Right, _, [.., R, Run(F, 1), Run(Q, 1)]) => {
            //     self.state = Left;
            //     self.right_tape.pop();
            //     add_or_merge_run(&mut self.left_tape, X, 1u128);
            //     self.right_tape.push(D);
            //     12u128
            // }
            // > P X -> > C P
            (Right, _, [.., Run(X, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, X);
                self.right_tape.push(P);
                self.right_tape.push(Run(C, 1u128));
                0u128
            }
            // > P D -> < D C
            (Right, _, [.., D, P]) => {
                self.state = Left;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, C, 1u128);
                self.right_tape.push(D);
                6u128
            }
            // > P C -> > F Q
            (Right, _, [.., Run(C, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, C);
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(Run(F, 1u128));
                0u128
            }
            // > P F -> > F P
            (Right, _, [.., Run(F, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, F);
                self.right_tape.push(P);
                self.right_tape.push(Run(F, 1u128));
                0u128
            }
            // > P P -> > F
            (Right, _, [.., P, P]) => {
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, F, 1u128);
                0u128
            }
            // > P Q -> > C
            (Right, _, [.., Run(Q, _), P]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                add_or_merge_run(&mut self.right_tape, C, 1u128);
                0u128
            }
            // > Q X -> > D P
            (Right, _, [.., Run(X, _), Run(Q, 1)]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, X);
                self.right_tape.push(P);
                self.right_tape.push(D);
                0u128
            }
            // > Q D -> > D Q
            (Right, _, [.., D, Run(Q, 1)]) => {
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                self.right_tape.push(D);
                0u128
            }
            // > Q C -> X > Q
            (Right, _, [.., Run(C, exp), Run(Q, 1)]) => {
                let n = *exp;
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, Q, 1);
                add_or_merge_run(&mut self.left_tape, X, n);
                4u128 * n
            }
            // > Q F -> > X P
            (Right, _, [.., Run(F, _), Run(Q, 1)]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, F);
                self.right_tape.push(P);
                self.right_tape.push(Run(X, 1u128));
                0u128
            }
            // > Q P -> > X
            (Right, _, [.., P, Run(Q, 1)]) => {
                self.right_tape.pop();
                self.right_tape.pop();
                add_or_merge_run(&mut self.right_tape, X, 1u128);
                0u128
            }
            // > Q Q -> > D (1/2)
            (Right, _, [.., Run(Q, 2u128..)]) => {
                decrease_run_by(&mut self.right_tape, Q, 2u128);
                self.right_tape.push(D);
                0u128
            }
            // > Q Q -> > D (2/2)
            (Right, _, [.., Run(Q, _), Run(Q, 1)]) => {
                self.right_tape.pop();
                decrement_run(&mut self.right_tape, Q);
                self.right_tape.push(D);
                0u128
            }
            // s> D -> Q > Q
            (RightSlow, _, [.., D]) => {
                self.state = Right;
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                add_or_merge_run(&mut self.right_tape, Q, 1u128);
                3u128
            }
            // s> C -> Q Q >
            (RightSlow, _, [.., Run(C, _)]) => {
                self.state = Right;
                decrement_run(&mut self.right_tape, C);
                add_or_merge_run(&mut self.left_tape, Q, 2u128);
                6u128
            }
            // s> F -> Q Q s>
            (RightSlow, _, [.., Run(F, _)]) => {
                decrement_run(&mut self.right_tape, F);
                add_or_merge_run(&mut self.left_tape, Q, 2u128);
                6u128
            }
            // s> P -> Q s>
            (RightSlow, _, [.., P]) => {
                self.right_tape.pop();
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                3u128
            }
            // s> Q -> Q >
            (RightSlow, _, [.., Run(Q, _)]) => {
                self.state = Right;
                decrement_run(&mut self.right_tape, Q);
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                3u128
            }
            // > *
            (Right, _, [.., Wildcard]) => {
                return Some(RightwardState::Normal);
            }
            // > P *
            (Right, _, [.., Wildcard, P]) => {
                return Some(RightwardState::P);
            }
            // > Q *
            (Right, _, [.., Wildcard, Run(Q, 1)]) => {
                return Some(RightwardState::Q);
            }
            // s> X -> Q > P
            (RightSlow, _, [.., Run(X, _)]) => {
                self.state = Right;
                decrement_run(&mut self.right_tape, X);
                add_or_merge_run(&mut self.left_tape, Q, 1u128);
                self.right_tape.push(P);
                3u128
            }
            // s> *
            (RightSlow, _, [.., Wildcard]) => {
                return Some(RightwardState::Slow);
            }
            _ => unreachable!(),
        };
        self.base_steps += n_steps;
        None
    }

    fn encode(&self) -> EncodedLTape {
        use BlockSymbol::Run;
        EncodedLTape(self.left_tape.iter().enumerate().map(
            |(i, block)| match block {
                Run(RunSymbolType::Q, exp) => {
                    assert!(i % 2 == 0);
                    u16::try_from(*exp).unwrap()
                }
                Run(RunSymbolType::X, exp) => {
                    assert!(i % 2 == 1);
                    u16::try_from(*exp).unwrap()
                }
                _ => unreachable!()
            }
        ).collect())
    }

    /// Returns a tuple of:
    /// * the final left tape encoded as a list of integers
    /// * the effect of running this InnerSimulation until the head goes back to the 
    /// right end again (also includes the left tape, this is a bit redundant)
    fn run_to_completion(mut self, memo: &mut Memo) -> (EncodedLTape, BlockInfo) {
        loop {
            if self.state == HigherState::Left {
                let BlockInfo {ltape, nadd, steps, rstate} = get_or_calculate(&self.encode(), memo);
                self.left_tape = ltape;
                rstate.update(&mut self.state, &mut self.right_tape);

                // Let N0 be the left exponent when this inner simulator was created.
                // The left exponent of this inner simulator is now N = N0 + Nadd.
                // The number of steps taken on the left side in this get_or_calculate() call is
                // steps = a0 + a1*N = a0 + a1 * (N0 + Nadd) = (a0 + a1*N0) + a1*Nadd.
                self.base_steps += steps;
                self.base_steps += steps.a1 * self.nadd;

                self.nadd += nadd;
            } else {
                if let Some(rstate) = self.basic_step() {
                    let pos_new = self.encode();
                    return (pos_new, BlockInfo {
                        ltape: self.left_tape,
                        nadd: self.nadd,
                        steps: self.base_steps,
                        rstate
                    });
                } else {
                    memo.steps += 1;
                }
            }
        }
    }
}

fn get_or_calculate(position: &EncodedLTape, memo: &mut Memo) -> BlockInfo {
    if let Some(info) = memo.positions.get(position) {
        return info.decode();
    }

    let mut sim = InnerSimulator::new(position);
    
    // run a step first so that it won't try to look up the same thing again
    sim.basic_step();
    memo.steps += 1;


    let (pos_new, answer) = sim.run_to_completion(memo);

    // if answer.rstate == RightwardState::Q {
    //     println!("new {:?} {}", position.0, &answer);
    // }

    let pinfo = PositionInfo {
        pos_new,
        nadd: answer.nadd,
        steps: answer.steps,
        rstate: answer.rstate,
    };

    memo.positions.insert(position.clone(), pinfo);
    answer
}

fn main() {
    try_outer_sim();
}

fn compare_accel() {
    let mut fast_sim = OuterSimulator::new(true);
    let mut slow_sim = OuterSimulator::new(false);

    let max_steps = 300;
    for i in 1..=max_steps {
        fast_sim.step().unwrap();
        while slow_sim.base_steps < fast_sim.base_steps {
            slow_sim.step().unwrap();
        }
        println!("{slow_sim}");
        println!("{fast_sim}");
    }
}

fn try_outer_sim() {
    let mut sim = OuterSimulator::new(true);

    let max_steps = 990; // u128 too small after ~1305 steps
    println!("{}", sim);
    for i in 1..=max_steps {
        let res = sim.step();
        println!("{}", sim);
    }
    println!("{}", sim);

    if let Some(memo) = sim.accelerator {
        println!("Cache: steps simulated {}, size {}", memo.steps, memo.positions.len());

        let mut counts: HashMap<RightwardState, u32> = HashMap::new();
        for v in memo.positions.values() {
            *counts.entry(v.rstate).or_default() += 1;
        }
        println!("# entries in cache, by the type of head produced to the right:");
        {
            use RightwardState::*;
            for s in [Normal, P, Q, Slow] {
                println!("  {}: {}", &s, counts.get(&s).unwrap());
            }
        }
    }
}

fn try_inner_sim() {
    let mut memo = Memo::new();

    let binfo = get_or_calculate(&EncodedLTape(vec![5,2,7,1,3,2,2,1,1]), &mut memo);
    println!("{binfo}");
    println!("Cache: steps simulated {}, size {}", memo.steps, memo.positions.len());
}