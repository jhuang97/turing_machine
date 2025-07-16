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
    let tm = TuringMachine::from_standard_notation("1RB2LA1LA_2LA0RA2RC_---0LC2RA");

    let always = |_: &BasicSimulator| true;
    let highlight = |sim: &BasicSimulator| {
        (sim.state == State::B && sim.prev_dir == Some(TMDirection::Right) && sim.tape.get(sim.position) == Some(&Symbol(1))) ||
        (sim.state == State::B && sim.prev_dir == Some(TMDirection::Right) && sim.tape.get(sim.position) == Some(&Symbol(2))) ||
        (sim.state == State::A && sim.prev_dir == Some(TMDirection::Left))
    };

    // run_basic_sim(&tm, 100, always);
    run_basic_sim(&tm, 2000, always);
}