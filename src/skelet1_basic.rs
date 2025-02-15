use std::{fmt, str::FromStr};
use std::collections::VecDeque;
use itertools::Itertools;

use crate::{check_transition_rule, BasicSimulator, BasicStepInfo, ConfigTransitionRule, State, Symbol, TMDirection, TuringMachine};

pub const SKELET_1: &str = "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC";

pub fn is_skelet1_basic_state(sim: &BasicSimulator) -> bool {
    use State::*;
    use TMDirection::*;
    (sim.state == A && sim.prev_dir == Some(Right) && (*sim.tape.get(sim.position).unwrap() == Symbol(1) || sim.position == sim.tape.len()-1)) ||
    (sim.state == C && sim.prev_dir == Some(Left))
}

pub fn is_skelet1_basic_state_alt(sim: &BasicSimulator) -> bool {
    use State::*;
    use TMDirection::*;
    (sim.state == A && sim.prev_dir == Some(Right) 
        && (sim.position == sim.tape.len()-1 || *sim.tape.get(sim.position  ).unwrap() == Symbol(1))
        &&  sim.position > 0                 && *sim.tape.get(sim.position-1).unwrap() == Symbol(1)
    ) ||
    (sim.state == C && sim.prev_dir == Some(Left))
}

#[derive(Clone)]
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

fn try_match_skelet1_single_tm(label: String, tm: &TuringMachine, basic_states: &Vec<PartialSimulatorState>, rules: &Vec<ConfigTransitionRule>) {
    let mut sim = BasicSimulator::new(tm.clone());
    let mut candidate_history: Vec<PartialSimulatorState> = Vec::new();
    for _ in 0..200 {
        sim.step();
        candidate_history.push(PartialSimulatorState::new(&sim, true));
    }

    let mut sk1_matches: Vec<bool> = Vec::new();
    let mut leftward_state: Option<State> = None;
    let mut rightward_state: Option<State> = None;
    let mut first_match: Option<PartialSimulatorState> = None;
    for b in basic_states {
        let mut matches = false;
        for c in &candidate_history {
            if b.partial_matches(c) {
                matches = true;
                match c.prev_dir {
                    TMDirection::Left => leftward_state = Some(c.state),
                    TMDirection::Right => rightward_state = Some(c.state),
                }
                if first_match.is_none() {
                    first_match = Some((*c).clone());
                }
                break;
            }
        }
        sk1_matches.push(matches);
    }

    let leftward_state = leftward_state.unwrap();
    let rightward_state = rightward_state.unwrap();

    let mut step_counts: Vec<usize> = Vec::new();
    for rule in rules {
        let mut rule2 = rule.clone();
        rule2.replace_state(leftward_state, rightward_state);

        step_counts.push(check_transition_rule(rule2, &tm, false).unwrap_or_else(|_| 0));
    }
    let counts_str = step_counts.iter().map(|n| if *n == 0 {":(".to_owned()} else { format!("{n:>2}") }).join(",");

    print!("{label}: {:?} {:?} {}; ", leftward_state, rightward_state, counts_str);

    match first_match {
        Some(sim_state) => print!("{sim_state}"),
        None => print!("--"),
    }
    
    // for m in sk1_matches {
    //     if m {
    //         print!("Y");
    //     } else {
    //         print!("_");
    //     }
    // }
    println!();
}

pub fn try_match_skelet1_basic_states() {
    let sk1 = TuringMachine::from_standard_notation(SKELET_1);
    let mut sk1_sim = BasicSimulator::new(sk1.clone());

    let candidates: &str = include_str!("../bb6_skelet1_equiv_candidates.txt").trim();
    let cand_tms: Vec<TuringMachine> = candidates.lines().map(|s| TuringMachine::from_standard_notation(s)).collect();

    let mut basic_states: Vec<PartialSimulatorState> = Vec::new();
    for _ in 0..200 {
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
    let rules_txt = include_str!("definitions/skelet1/config_transition_rules.txt");
    let rules: Vec<_> = rules_txt.lines()
        .filter(|s| s.len() > 1)
        .map(|s| ConfigTransitionRule::from_str(s).unwrap())
        .collect();

    try_match_skelet1_single_tm("Skelet 1".to_owned(), &sk1, &basic_states, &rules);
    println!("----------");

    for (i, tm) in cand_tms.into_iter().enumerate() {
        try_match_skelet1_single_tm(format!("{i:>8}"), &tm, &basic_states, &rules);
    }
}

pub fn try_match_skelet1_basic_states_candidate_7() {
    let sk1 = TuringMachine::from_standard_notation(SKELET_1);
    let mut sk1_sim = BasicSimulator::new(sk1.clone());

    let mut basic_states: Vec<PartialSimulatorState> = Vec::new();
    for _ in 0..400 {
        let BasicStepInfo { halted, record: _} = sk1_sim.step();
        assert!(!halted);

        if is_skelet1_basic_state(&sk1_sim) {
            basic_states.push(PartialSimulatorState::new(&sk1_sim, true));
        }
    }

    let tm = TuringMachine::from_standard_notation("1RB0LF_1LC0RC_1RA1LD_0RE0LB_---1RC_1RD1RF");
    let mut sim = BasicSimulator::new(tm.clone());
    let mut candidate_history: Vec<PartialSimulatorState> = Vec::new();
    for _ in 0..400 {
        sim.step();
        candidate_history.push(PartialSimulatorState::new(&sim, true));
    }

    let mut sk1_matches: Vec<bool> = Vec::new();
    // let mut leftward_state: Option<State> = None;
    // let mut rightward_state: Option<State> = None;
    for b in basic_states {
        let mut matches = false;
        for c in &candidate_history {
            if b.partial_matches(c) {
                matches = true;
                // match c.prev_dir {
                //     TMDirection::Left => leftward_state = Some(c.state),
                //     TMDirection::Right => rightward_state = Some(c.state),
                // }
                println!("{b}");
                println!("{c}");
                break;
            }
        }
        sk1_matches.push(matches);
    }
}

pub fn try_match_skelet1_basic_states_alt() {
    let sk1 = TuringMachine::from_standard_notation(SKELET_1);
    let mut sk1_sim = BasicSimulator::new(sk1.clone());

    let candidates: &str = include_str!("../bb6_skelet1_equiv_candidates.txt").trim();
    let cand_tms: Vec<TuringMachine> = candidates.lines().map(|s| TuringMachine::from_standard_notation(s)).collect();

    let mut basic_states: Vec<PartialSimulatorState> = Vec::new();
    for _ in 0..200 {
        let BasicStepInfo { halted, record: _} = sk1_sim.step();
        assert!(!halted);

        if is_skelet1_basic_state_alt(&sk1_sim) {
            basic_states.push(PartialSimulatorState::new(&sk1_sim, true));
        }
    }

    // for b in &basic_states {
    //     println!("{}", b);
    // }
    // println!("{}", basic_states.len());
    let rules_txt = include_str!("definitions/skelet1/config_transition_rules_alt.txt");
    let rules: Vec<_> = rules_txt.lines()
        .filter(|s| s.len() > 1)
        .map(|s| ConfigTransitionRule::from_str(s).unwrap())
        .collect();

    try_match_skelet1_single_tm("Skelet 1".to_owned(), &sk1, &basic_states, &rules);
    println!("----------");

    for (i, tm) in cand_tms.into_iter().enumerate() {
        try_match_skelet1_single_tm(format!("{i:>8}"), &tm, &basic_states, &rules);
    }
}