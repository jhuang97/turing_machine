use std::env;

use turing_machine::{BasicSimulator, BasicStepInfo, State, Symbol, TMDirection, TuringMachine};

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
    let tm = TuringMachine::from_standard_notation("1RB1RC_0RC0LD_1LD1RA_0LE1LF_---1RA_0LG0LA_1LB0RB");

    let always = |_: &BasicSimulator| true;
    let highlight = |sim: &BasicSimulator| {
        (sim.state == State::C && sim.prev_dir == Some(TMDirection::Right) && sim.tape.get(sim.position) == Some(&Symbol(1))) ||
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Left) && sim.tape.get(sim.position+1) == Some(&Symbol(0)))
    };

    // (1 <A 01)|(011 B> 1)|(1 A> 11)|(11 <B 10)

    run_basic_sim(&tm, 4320, always);
    // run_basic_sim(&tm, 1000, highlight);
}