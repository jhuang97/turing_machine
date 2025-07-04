use std::env;
use std::str::FromStr;
use turing_machine::check_transition_rule;
use turing_machine::skelet1;
use turing_machine::skelet1_basic;
use skelet1::{counter_to_rle, counter_transition_rules, measure_uni_cycle, BigInt, CounterBlockType, CounterStepInfo, CounterSymbol, Direction};
use skelet1_basic::{SKELET_1, is_skelet1_basic_state};
use turing_machine::ConfigTransitionRule;
use turing_machine::DirectedHeadSimulator;
use turing_machine::{BasicSimulator, BasicStepInfo, State, Symbol, TMDirection, TMTransition, TuringMachine, DirectedHeadConfig, DirectedHeadStepResult};

const TM_13502512: &str = "1RB1LD_1LC1RE_---1LD_1LA0LD_0RE0RC";
const HALT_105: &str = "1RB1LC_0LB1LA_1RD1LB_1RE0RD_0RA---";


/// incomplete
fn detect_rightward_translated_cycling_with_records(sim: &BasicSimulator, max_steps: usize) {
    use itertools::izip;

    let mut sim0 = sim.clone();

    let mut record_steps: Vec<usize> = Vec::new();
    let mut record_positions: Vec<i64> = Vec::new();
    let mut distances_back: Vec<i64> = Vec::new();
    for _ in 0..max_steps {
        let BasicStepInfo { halted: _, record} = sim0.step();
        let curr_pos = sim0.absolute_position();
        
        for (&record_pos, distance_back) in record_positions.iter().zip(distances_back.iter_mut()) {
            if curr_pos < record_pos {
                let dist = record_pos - curr_pos;
                *distance_back = (*distance_back).max(dist);
            }
        }

        if record == Some(TMDirection::Right) {
            // println!("{} *", sim.display_directed_head());
            record_steps.push(sim0.time);
            record_positions.push(sim0.absolute_position());
            distances_back.push(0);
        }
    }

    for (a, b, c) in izip!(&record_steps, &record_positions, &distances_back) {
        println!("time: {a}, pos: {b}, dist back: {c}");
    }

    let max_dist_back = distances_back.iter().max();
    if let Some(&max_dist_back) = max_dist_back {
        // run the simulation again and check on the record configurations
        let mut sim0 = sim.clone();
        let mut record_states: Vec<State> = Vec::new();
        let mut record_local_tapes: Vec<Vec<Symbol>> = Vec::new();

        for (i, &rec_time) in record_steps.iter().enumerate() {
            while sim0.time < rec_time {
                sim0.step();
            }

            todo!()
        }
    } else {
        println!("oh no");
    }
}

fn is_bicycle_leftward_stride_state(sim: &BasicSimulator) -> bool {
    use State::*;
    use TMDirection::*;
    sim.state == A && (sim.prev_dir == Some(Left)) && sim.position == sim.tape.len()-3
    && (*sim.tape.back().unwrap() == Symbol(1))
    && (*sim.tape.get(sim.tape.len()-2).unwrap() == Symbol(2))
}

fn is_bicycle_right_end_state(sim: &BasicSimulator) -> bool {
    use State::*;
    use TMDirection::*;
    sim.state == A && (sim.prev_dir == Some(Right)) && sim.position == sim.tape.len()-2
    && (*sim.tape.back().unwrap() == Symbol(1))
    && (*sim.tape.get(sim.tape.len()-2).unwrap() == Symbol(2))
}
fn main() {
    // let tm = TuringMachine::from_standard_notation("1RB1RF_1RC0RE_0LD1RE_---1LE_1RA1LF_0RC0LB");
    // let tm = TuringMachine::from_standard_notation("1RB1RE_1RC0RD_0LC1LD_1RA1LE_0RF0LB_---1RD");
    // let tm = TuringMachine::from_standard_notation("1RB---_1LC0RC_1RF1LD_0RE0LB_---1RC_1RB1RD");
    // let tm = TuringMachine::from_standard_notation("1RB2LA0RB1LB---_1LA3RA1RA4LB2RB");

    // let mut sim = BasicSimulator::new(tm);
    // println!("{}", sim.display_directed_head());
    // for k in 0..40000000000u64 {
    //     let BasicStepInfo { halted, record: _} = sim.step();

    //     // if k < 10 || sim.tape.contains(&Symbol(4)) || (k & (k-1) == 0) || halted {
    //     //     println!("{}", sim.display_directed_head());
    //     // }
    //     if is_bicycle_leftward_stride_state(&sim) || is_bicycle_right_end_state(&sim) {
    //         println!("{}", sim.display_directed_head());
    //     }
    //     if halted {
    //         break;
    //     }
    // }

    // {
    //     let init_config = DirectedHeadConfig::from_str("023 <A").unwrap();

    //     println!("{}", &init_config);
    //     let mut sim = DirectedHeadSimulator::new(&init_config, &tm);
    
    //     loop {
    //         let res = sim.step();
    //         print!("{}: {} ", &sim.time, &sim.config);
    
    //         match res {
    //             DirectedHeadStepResult::Success => println!(),
    //             _ => { println!("{:?}", res); break }
    //         }
    //     }
    // }
    

    // let tm = TuringMachine::from_standard_notation("1RB0RE_0LC1RC_0RD1LA_1LE---_1LB1RC");
    // let mut sim = BasicSimulator::new(tm);
    // detect_rightward_translated_cycling_with_records(&sim, 60);
}