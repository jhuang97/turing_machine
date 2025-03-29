use std::{env, str::FromStr};

use turing_machine::{check_transition_rule, BasicSimulator, BasicStepInfo, CheckerVerbosity, ConfigTransitionRule, State, Symbol, TMDirection, TuringMachine};

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

fn main() {
    env::set_var("RUST_BACKTRACE", "1");

    let candidates_s: Vec<_> = include_str!("../../bb6_Sk1-like.txt").trim().lines().collect();
    let candidates: Vec<_> = candidates_s.iter().map(|s| TuringMachine::from_standard_notation(s)).collect();

    let tm_idx = 3;
    println!("{}", candidates_s[tm_idx]);

    let tm = candidates[tm_idx].clone();

    // 10A>, 1<E01

    let rules_guess = 
"10A> 0000 -> 1<E01 001
10A> 0001 -> 1010 10A>
10A> 001000 -> 10 1<E01 001
10A> 00110 -> 1<E01 0011
10A> 00111 -> 10110 10A>
10A> 01000 -> 1<E01 0011
10A> 01001 -> 10110 10A>
000 10A> 01010 -> 10 1<E01 00100
10A> 01011 -> 1011 1<E01
10A> 1 -> 1<E01
00000 1<E01 -> 10 10A> 0011
00010000 1<E01 -> 10 10A> 0010011
1000 1<E01 -> 1<E01 0011
000100 1<E01 -> 10 10A> 00111
10100 1<E01 -> 1<E01 00111
101100 1<E01 -> 1<E01 001111
00010 1<E01 -> 10 10A> 0001
1010 1<E01 -> 1<E01 0001
000110 1<E01 -> 10 10A> 00101
10110 1<E01 -> 1<E01 00101
101110 1<E01 -> 1<E01 001101
10001 1<E01 -> 1<E01 00101
10101 1<E01 -> 1<E01 00001";

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
    let highlight3 = |sim: &BasicSimulator| {
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Right)) ||
        (sim.state == State::C && sim.prev_dir == Some(TMDirection::Left)) ||
        (sim.state == State::B && sim.prev_dir == Some(TMDirection::Left))
    };
    let highlight3a = |sim: &BasicSimulator| {
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Right) && sim.tape.get(sim.position) == Some(&Symbol(0))) ||
        (sim.state == State::C && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position+1) == Some(&Symbol(0))) ||
        (sim.state == State::B && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position+1) == Some(&Symbol(1)) && sim.tape.get(sim.position+2) == Some(&Symbol(0)))
    };
    let highlight3b = |sim: &BasicSimulator| {
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Right) && sim.tape.get(sim.position) == Some(&Symbol(0))) ||
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position) == Some(&Symbol(1)))
    };
    let highlight4 = |sim: &BasicSimulator| {
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Right) && sim.tape.get(sim.position-1) == Some(&Symbol(0))
        && sim.tape.get(sim.position-2) == Some(&Symbol(1))) ||
        (sim.state == State::E && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position) == Some(&Symbol(1))
        && sim.tape.get(sim.position+1) == Some(&Symbol(0)) && sim.tape.get(sim.position+2) == Some(&Symbol(1)))
    };
    let highlight_right_end = |sim: &BasicSimulator| {
        ((sim.state == State::D && sim.prev_dir == Some(TMDirection::Right)) ||
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position+1) == Some(&Symbol(1))))
        && sim.position > sim.tape.len() - 10
    };
    run_basic_sim(&tm, 5000, highlight4);

    // let mut sim = BasicSimulator::new(tm);
    // println!("{}", sim.display_directed_head());
    // for _ in 0..2000 {
    //     let BasicStepInfo { halted: _, record} = sim.step();
    //     println!("{}", sim.display_directed_head());
    // }
}