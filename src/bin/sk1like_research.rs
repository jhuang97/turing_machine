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

    let tm_idx = 2;
    println!("{}", candidates_s[tm_idx]);

    let tm = candidates[tm_idx].clone();

    // D> 011 -> *HALT*

    let rules_guess = 
"A>0 110 -> 100 A>0
A>0 111 -> 1<A 110
0000 A>0 0 -> 1<A 11011
01 A>0 0 -> 100 A>0
000010 A>0 0 -> 1<A 1101111
1110 A>0 0 -> 1<A 11011
10100 A>0 0 -> 1<A 111111
11 A>0 0 -> 1<A 110
000 1<A -> 100 A>0
100 1<A -> 1<A 110
1 11<A -> 00 A>0
0000 11<A -> 1<A 11010
000010 11<A -> 1<A 1101110
0110 11<A -> 100 A>0 10
1110 11<A -> 1<A 11010
00100 11<A -> 1<A 110110
001100 11<A -> 1<A 1101110";

// not closed?
// A>0 101
// 1010 A>0 0
// 1100 A>0 0
// 010 1<A
// 110 1<A

//halt
//A>0 100 -> F>";

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
    let highlight_right_end = |sim: &BasicSimulator| {
        ((sim.state == State::D && sim.prev_dir == Some(TMDirection::Right)) ||
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position+1) == Some(&Symbol(1))))
        && sim.position > sim.tape.len() - 10
    };
    run_basic_sim(&tm, 6000, highlight3b);

    // let mut sim = BasicSimulator::new(tm);
    // println!("{}", sim.display_directed_head());
    // for _ in 0..2000 {
    //     let BasicStepInfo { halted: _, record} = sim.step();
    //     println!("{}", sim.display_directed_head());
    // }
}