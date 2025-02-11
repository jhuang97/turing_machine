use std::fmt;
use std::collections::VecDeque;

use crate::{TuringMachine, State, Symbol, TMDirection, BasicSimulator, BasicStepInfo};

pub const SKELET_1: &str = "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC";

pub fn is_skelet1_basic_state(sim: &BasicSimulator) -> bool {
    use State::*;
    use TMDirection::*;
    (sim.state == A && sim.prev_dir == Some(Right) && (*sim.tape.get(sim.position).unwrap() == Symbol(1) || sim.position == sim.tape.len()-1)) ||
    (sim.state == C && sim.prev_dir == Some(Left))
}

struct PartialSimulatorState {
    tape: VecDeque<Symbol>,
    position: usize,
    prev_dir: TMDirection,
    state: State
}

impl fmt::Display for PartialSimulatorState {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let split_pos = match self.prev_dir {
            TMDirection::Left => self.position + 1,
            TMDirection::Right => self.position,
        };
        for i in 0..split_pos {
            write!(f, "{}", self.tape.get(i).unwrap().0)?;
        }
        match self.prev_dir {
            TMDirection::Left => write!(f, " <{:?} ", self.state)?,
            TMDirection::Right => write!(f, " {:?}> ", self.state)?,
        }
        for i in split_pos..self.tape.len() {
            write!(f, "{}", self.tape.get(i).unwrap().0)?;
        }

        Ok(())
    }
}

impl PartialSimulatorState {
    pub fn new(sim: &BasicSimulator, strip: bool) -> Self {
        let mut tape = sim.tape.clone();
        let mut position = sim.position;

        if strip {
            while tape.back() == Some(&Symbol(0)) {
                tape.pop_back();
            }
            while tape.front() == Some(&Symbol(0)) {
                tape.pop_front();
                position -= 1;
            }
        }

        PartialSimulatorState {
            tape,
            position,
            prev_dir: sim.prev_dir.unwrap(),
            state: sim.state
        }
    }

    pub fn partial_matches(&self, other: &Self) -> bool {
        (self.tape == other.tape) 
        && (self.position == other.position) 
        && (self.prev_dir == other.prev_dir)
    }
}

pub fn try_match_skelet1_basic_states() {
    let sk1 = TuringMachine::from_standard_notation(SKELET_1);
    let mut sk1_sim = BasicSimulator::new(sk1);

    let candidates: &str = include_str!("../bb6_skelet1_equiv_candidates.txt").trim();
    let cand_tms: Vec<TuringMachine> = candidates.lines().map(|s| TuringMachine::from_standard_notation(s)).collect();

    let mut basic_states: Vec<PartialSimulatorState> = Vec::new();
    for _ in 0..400 {
        let BasicStepInfo { halted, record: _} = sk1_sim.step();
        assert!(!halted);

        if is_skelet1_basic_state(&sk1_sim) {
            basic_states.push(PartialSimulatorState::new(&sk1_sim, true));
        }
    }

    // for b in &basic_states {
    //     println!("{}", b);
    // }
    // println!("{}", basic_states.len());

    for (i, tm) in cand_tms.into_iter().enumerate() {
        let mut sim = BasicSimulator::new(tm);
        let mut candidate_history: Vec<PartialSimulatorState> = Vec::new();
        for _ in 0..400 {
            sim.step();
            candidate_history.push(PartialSimulatorState::new(&sim, true));
        }

        let mut sk1_matches: Vec<bool> = Vec::new();
        for b in &basic_states {
            let mut matches = false;
            for c in &candidate_history {
                if b.partial_matches(c) {
                    matches = true;
                    break;
                }
            }
            sk1_matches.push(matches);
        }
        print!("{i}: ");
        for m in sk1_matches {
            if m {
                print!("Y");
            } else {
                print!("_");
            }
        }
        println!();
    }
}