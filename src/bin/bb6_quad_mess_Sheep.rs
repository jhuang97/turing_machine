use turing_machine::{CheckerVerbosity, ConfigTransitionRule, DirectedHeadConfig, DirectedHeadStepResult, GeneralSymbol, Symbol, TMDirection, TuringMachine, check_transition_rule, run_to_undefined};

fn end_ones(n: usize) -> Vec<GeneralSymbol> {
    let mut v = vec![GeneralSymbol::End];
    for _ in 0..n {
        v.push(GeneralSymbol::Basic(Symbol(1)));
    }
    v
}

fn c(m: usize, n: usize) -> DirectedHeadConfig {
    DirectedHeadConfig {
        left_tape: end_ones(m),
        right_tape: end_ones(n),
        dir: TMDirection::Right,
        state: turing_machine::State::E,
    }
}

fn cleft(m: usize, n: usize) -> DirectedHeadConfig {
    DirectedHeadConfig {
        left_tape: end_ones(m+1),
        right_tape: end_ones(n-1),
        dir: TMDirection::Left,
        state: turing_machine::State::E,
    }
}

fn check_low_level_rules() {
    let tm = TuringMachine::from_standard_notation("1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE");

    run_to_undefined(c(0,0), &tm, CheckerVerbosity::Off).unwrap();

    for n in 1..=50 {
        run_to_undefined(c(1, n), &tm, CheckerVerbosity::Off).unwrap();
    }

    for n in 1..=50 {
        let rule = ConfigTransitionRule { before: c(0, n), after: c(2, n-1) };
        check_transition_rule(rule, &tm, CheckerVerbosity::Off).unwrap();
    }

    for m in 1..=10 {
        for n in 1..=10 {
            let rule = ConfigTransitionRule { before: c(2*m, n), after: c(3*m + n - 1, 2) };
            check_transition_rule(rule, &tm, CheckerVerbosity::Off).unwrap();
        }
    }

    for m in 1..10 {
        for n in 1..10 {
            let rule = ConfigTransitionRule { before: c(2*m+1, n), after: cleft(m-1, m+n+3) };
            check_transition_rule(rule, &tm, CheckerVerbosity::Off).unwrap();
        }
    }

    // for m in 1..=20 {
    //     print!("m {m:5}: ");
    //     for n in 1..=10 {
    //         let rule = ConfigTransitionRule { before: c(2*m+1, n), after: c(m-1, m+n+3) };
    //         // check_transition_rule(rule, &tm, CheckerVerbosity::All).unwrap();
    //         let res = check_transition_rule(rule, &tm, CheckerVerbosity::Off);
    //         match res {
    //             Ok(_) => print!("O"),
    //             Err(DirectedHeadStepResult::Success) => unreachable!(),
    //             Err(DirectedHeadStepResult::OutOfTime) => print!("t"),
    //             Err(DirectedHeadStepResult::RanOffTape) => print!("x"),
    //             Err(DirectedHeadStepResult::Undefined) => print!("H"),
    //         }
    //     }
    //     println!();
    // }
}

fn advance_rule_2((a, n): (u128, u128)) -> Option<(u128, u128)> {
    if a < 3 {
        unimplemented!();
    }
    if a == 4 {
        None
    } else if a == 3 {
        if n == 0 {
            None
        } else {
            Some((5, n-1))
        }
    } else if a % 2 == 1 {
        let m = (a + 1) / 2;
        Some((3*m + n - 4, 2))
    } else {
        let m = a / 2;
        Some((m, m+n+1))
    }
}

fn main() {
    let tm = TuringMachine::from_standard_notation("1RB1LA_0LC0RC_1LE1RD_1RE1RC_1LF0LA_---1LE");

    // check_low_level_rules();

    let mut state = Some((5, 2));
    for k in 0..=1000 {
        if let Some(s) = state {
            println!("{} {}", s.0, s.1);
            state = advance_rule_2(s);
        } else {
            break;
        }
    }
}