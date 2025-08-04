use turing_machine::{
    skelet1::{CounterBlockType, CounterSimulator, CounterStepInfo, CounterSymbol, Direction}, 
    skelet1_basic::{is_skelet1_basic_state, SKELET_1}, 
    BasicSimulator, State, TMDirection, TuringMachine};

fn main() {
    // figure_out_starting_tape_counter();
    // run_sk1();
    // run_simX1();
    // run_simY();
    run_simZ();
}

fn run_sk1() {
    use std::time::Instant;
    let now = Instant::now();

    use CounterBlockType::*;
    use CounterSymbol::*;

    let mut sim = CounterSimulator::new(true, true);
    let mut num_uni_cycle_rules = 0;

    for i in 0..85257345 {
        let res = sim.step().unwrap();

        let is_uni = matches!(res, CounterStepInfo::UniCycle(_));
        if is_uni {
            num_uni_cycle_rules += 1;
        }
        if i % 1000000 == 0 || (i > 85256360 && (sim.right_tape.len() > 30 || i < 85256369)) {
            println!("{num_uni_cycle_rules} uni cycle(s); {sim}");
        }
    }
}

fn run_simX1() {
    use std::time::Instant;
    let now = Instant::now();

    use CounterBlockType::*;
    use CounterSymbol::*;

    let mut sim = CounterSimulator::new_from_alt_trajectory(
        vec![L, X(1)], vec![R, X(1), C], Direction::Right);
    
    let mut num_uni_cycle_rules = 0;

    for i in 0..16000 {
        let res = sim.step().unwrap();

        let is_uni = matches!(res, CounterStepInfo::UniCycle(_));
        if is_uni {
            num_uni_cycle_rules += 1;
        }
        if i % 1000 == 0 || (i > 14000 && sim.right_tape.len() > 30) {
            println!("{num_uni_cycle_rules} uni cycle(s); {sim}");
        }
    }
}

fn run_simY() {
    use std::time::Instant;
    let now = Instant::now();

    use CounterBlockType::*;
    use CounterSymbol::*;

    let mut sim = CounterSimulator::new_from_alt_trajectory(
        vec![L, C1], vec![R, D], Direction::Right);
    
    let mut num_uni_cycle_rules = 0;

    for i in 0..721560 {
        let res = sim.step().unwrap();

        let is_uni = matches!(res, CounterStepInfo::UniCycle(_));
        if is_uni {
            num_uni_cycle_rules += 1;
        }
        if i % 1000 == 0 || (i > 720000 && sim.right_tape.len() > 25) {
            println!("{num_uni_cycle_rules} uni cycle(s); {sim}");
        }
    }
}

/// trajectory Z seems more complicated, haven't figured out what's going on
fn run_simZ() {
    use std::time::Instant;
    let now = Instant::now();

    use CounterBlockType::*;
    use CounterSymbol::*;

    let mut sim = CounterSimulator::new_from_alt_trajectory(
        vec![L, X(1)], vec![R, C], Direction::Right);
    
    let mut num_uni_cycle_rules = 0;

    let print_thresh = 59328500; // 8_700_000;

    for i in 0..59332000 {
        let res = sim.step().unwrap();

        let is_uni = matches!(res, CounterStepInfo::UniCycle(_));
        if is_uni {
            num_uni_cycle_rules += 1;
        }
        if i % 1000000 == 0 || (i > print_thresh && sim.right_tape.len() > 30) {
            let mut sim_uni_p = sim.clone();
            sim_uni_p.rewrite_with_blocks(&vec![], &vec![M]);
            println!("{num_uni_cycle_rules} uni cycle(s); {sim_uni_p}");
            // println!("{num_uni_cycle_rules} uni cycle(s); {sim}");
        }
    }

    let elapsed = now.elapsed();
    println!("Elapsed: {:.2?}", elapsed);
}

fn figure_out_starting_tape_counter() {
    let tm = TuringMachine::from_standard_notation(SKELET_1);

    let mut simX1 = BasicSimulator::from_tape(tm.clone(), 
        &[1,1,0,1], State::A, 2, Some(TMDirection::Right));

    let mut simY = BasicSimulator::from_tape(tm.clone(), 
        &[1,1,0,1], State::B, 3, Some(TMDirection::Right));

    let mut simZ = BasicSimulator::from_tape(tm.clone(), 
        &[1,0,1,1], State::E, 3, Some(TMDirection::Right));

    for sim in [simX1, simY, simZ].iter_mut() {
        println!("{}", sim.display_directed_head());

        let mut steps = 0;
        loop {
            sim.step();

            if is_skelet1_basic_state(&sim) {
                println!("{}", sim.display_directed_head());
                steps += 1;
            }

            if steps > 60 {
                break;
            }
        }

        println!("-----");
    }
    // println!("{}", simX1.display_directed_head());
    // println!("{}", simY.display_directed_head());
    // println!("{}", simZ.display_directed_head());
}