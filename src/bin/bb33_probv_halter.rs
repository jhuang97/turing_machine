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
    run_basic_sim(&tm, 5000, basic_state);

    // let mut sim = BasicSimulator::new(tm);
    // println!("{}", sim.display_directed_head());
    // for _ in 0..2000 {
    //     let BasicStepInfo { halted: _, record} = sim.step();
    //     println!("{}", sim.display_directed_head());
    // }
}