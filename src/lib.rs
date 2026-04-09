pub mod skelet1;
pub mod skelet1_basic;
pub mod wily_coyote;

use core::str;
use std::fmt;
use std::str::FromStr;
use std::collections::VecDeque;
use itertools::Itertools;
use strum_macros::EnumString;

#[derive(Debug, Clone)]
pub struct TuringMachine {
    transitions: Vec<Vec<Option<TMTransition>>>,
}

impl TuringMachine {
    pub fn from_standard_notation(s: &str) -> Self {
        let parts: Vec<&str> = s.split('_').collect();
        let n_states = parts.len();
        let n_char = parts[0].len();
        assert!(n_char % 3 == 0);
        let n_symbols = (n_char / 3) as u8;
    
        for part in &parts {
            assert!(part.len() == n_symbols as usize * 3);
        }

        let transitions = parts.iter()
            .map(|&row| row.as_bytes().chunks(3).map(str::from_utf8)
                .map(|s| {
                    let s1 = s.unwrap();
                    if s1.chars().next().unwrap() == '-' {
                        None
                    } else {
                        Some(TMTransition::from_str(s1).unwrap())
                    }
                })
                .collect::<Vec<_>>())
            .collect::<Vec<_>>();
    
        assert_eq!(transitions.len(), n_states);
        assert_eq!(transitions[0].len(), n_symbols as usize);

        TuringMachine { transitions }
    }

    pub fn n_states(&self) -> usize {
        self.transitions.len()
    }

    pub fn n_symbols(&self) -> usize {
        self.transitions[0].len()
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub struct Symbol(pub u8);

#[derive(Debug, Clone)]
pub struct TMTransition {
    new_symbol: Symbol,
    direction: TMDirection,
    new_state: State
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseTMTransitionError;

impl FromStr for TMTransition {
    type Err = ParseTMTransitionError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let mut c = s.chars();
        let symbol_idx = c.next().unwrap().to_string().parse::<u8>().map_err(|_| ParseTMTransitionError)?;
        let direction = TMDirection::from_str(&c.next().unwrap().to_string())
            .map_err(|_| ParseTMTransitionError)?;
        let new_state = State::from_str(&c.next().unwrap().to_string())
            .map_err(|_| ParseTMTransitionError)?;
        Ok(Self {
            new_symbol: Symbol(symbol_idx),
            direction,
            new_state
        })
    }
}

#[derive(Debug, PartialEq, Eq, EnumString, Copy, Clone)]
pub enum TMDirection {
    #[strum(serialize = "L")]
    Left,
    #[strum(serialize = "R")]
    Right
}

#[derive(Debug, PartialEq, Eq, EnumString, Copy, Clone)]
pub enum State {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
    F = 5,
    G = 6,
}

const STATES: [State; 7] = [State::A, State::B, State::C, State::D, State::E, State::F, State::G];

pub struct BasicStepInfo {
    pub halted: bool,
    pub record: Option<TMDirection>,
}

#[derive(Clone)]
pub struct BasicSimulator {
    tm: TuringMachine,
    pub tape: VecDeque<Symbol>,
    pub state: State,
    pub position: usize,
    pub time: usize,
    pub halted: bool,
    pub prev_dir: Option<TMDirection>,
    pub start_position: usize,
}

impl BasicSimulator {
    pub fn new(tm: TuringMachine) -> Self {
        Self {
            tm,
            tape: VecDeque::from([Symbol(0)]),
            state: State::A,
            position: 0,
            time: 0,
            halted: false,
            prev_dir: None,
            start_position: 0,
        }
    }

    pub fn from_tape(tm: TuringMachine, tape: &[u8], state: State, position: usize, prev_dir: Option<TMDirection>) -> Self {
        Self {
            tm,
            tape: tape.iter().map(|&x| Symbol(x)).collect(),
            state,
            position,
            time: 0,
            halted: false,
            prev_dir,
            start_position: position
        }
    }

    pub fn step(&mut self) -> BasicStepInfo {
        if self.halted {
            return BasicStepInfo { halted: true, record: None };
        }

        self.time += 1;
        let cell = self.tape.get_mut(self.position).unwrap();

        if let Some(transition) = &self.tm.transitions[self.state as usize][cell.0 as usize] {
            *cell = transition.new_symbol;
            self.state = transition.new_state;

            let mut record: Option<TMDirection> = None;

            match transition.direction {
                TMDirection::Left => {
                    if self.position == 0 {
                        self.tape.push_front(Symbol(0));
                        self.start_position += 1;
                        record = Some(TMDirection::Left);
                    } else {
                        self.position -= 1;
                    }
                },
                TMDirection::Right => {
                    if self.position == self.tape.len()-1 {
                        self.tape.push_back(Symbol(0));
                        record = Some(TMDirection::Right);
                    }
                    self.position += 1;
                }
            }
            self.prev_dir = Some(transition.direction);

            BasicStepInfo { halted: false, record }
        } else {
            self.halted = true;
            BasicStepInfo { halted: true, record: None }
        }
    }

    pub fn display_directed_head(&self) -> impl fmt::Display + '_ {
        DirectedHead(self)
    }

    pub fn absolute_position(&self) -> i64 {
        (self.position as i64) - (self.start_position as i64)
    }
}

impl fmt::Display for BasicSimulator {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let t_s = self.time.to_string();
        let mut left_width = t_s.len() + 1;
        if self.halted {
            left_width = left_width.max(5);
        }
        write!(f, "{:<left_width$}{:>width$}\n", t_s, format!("{:?}", self.state), width=self.position + 1)?;
        write!(f, "{:<left_width$}", if self.halted { "HALT" } else {""})?;
        for symb in &self.tape {
            write!(f, "{}", symb.0)?;
        }
        Ok(())
    }
}

struct DirectedHead<'a>(&'a BasicSimulator);

impl fmt::Display for DirectedHead<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}: ", self.0.time)?;
        if let Some(d) = self.0.prev_dir {
            let split_pos = match d {
                TMDirection::Left => self.0.position + 1,
                TMDirection::Right => self.0.position,
            };
            for i in 0..split_pos {
                write!(f, "{}", self.0.tape.get(i).unwrap().0)?;
            }
            match d {
                TMDirection::Left => write!(f, " <{:?} ", self.0.state)?,
                TMDirection::Right => write!(f, " {:?}> ", self.0.state)?,
            }
            for i in split_pos..self.0.tape.len() {
                write!(f, "{}", self.0.tape.get(i).unwrap().0)?;
            }
        } else {
            for i in 0..self.0.position {
                write!(f, "{}", self.0.tape.get(i).unwrap().0)?;
            }
            write!(f, "({:?}{})", self.0.state, self.0.tape.get(self.0.position).unwrap().0)?;
            for i in self.0.position+1..self.0.tape.len() {
                write!(f, "{}", self.0.tape.get(i).unwrap().0)?;
            }
        }

        if self.0.halted {
            write!(f, " HALT")?;
        }

        Ok(())
    }
}

#[derive(Debug, Copy, Clone, Eq, PartialEq)]
pub enum GeneralSymbol {
    Basic(Symbol),
    Wildcard,
    End
}

impl fmt::Display for GeneralSymbol {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self {
            GeneralSymbol::Basic(s) => write!(f, "{}", s.0)?,
            GeneralSymbol::Wildcard => write!(f, "*")?,
            GeneralSymbol::End => write!(f, "$")?,
        }
        Ok(())
    }
}

#[derive(Eq, PartialEq, Clone)]
pub struct DirectedHeadConfig {
    pub left_tape: Vec<GeneralSymbol>,
    pub right_tape: Vec<GeneralSymbol>,
    pub dir: TMDirection,
    pub state: State,
}

impl DirectedHeadConfig {
    fn replace_state(&mut self, leftward_state: State, rightward_state: State) {
        match self.dir {
            TMDirection::Left => self.state = leftward_state,
            TMDirection::Right => self.state = rightward_state,
        }
    }
}

#[derive(Clone)]
pub struct ConfigTransitionRule {
    pub before: DirectedHeadConfig,
    pub after: DirectedHeadConfig
}

impl ConfigTransitionRule {
    pub fn replace_state(&mut self, leftward_state: State, rightward_state: State) {
        self.before.replace_state(leftward_state, rightward_state);
        self.after.replace_state(leftward_state, rightward_state);
    }
}

impl FromStr for ConfigTransitionRule {
    type Err = ParseConfigError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (s1, s2) = s.split_once(" -> ").ok_or(ParseConfigError::NoArrowDelimiter)?;
        let before = DirectedHeadConfig::from_str(s1)?;
        let after = DirectedHeadConfig::from_str(s2)?;
        Ok(Self { before, after })
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseConfigError {
    NoArrowDelimiter,
    NoHead,
    NoState,
    BadState,
    BadSymbol
}

impl DirectedHeadConfig {
    pub fn parse_str(s: &str, enforce_end_wildcards: bool) -> Result<Self, ParseConfigError> {
        let cs = s.chars().filter(|&c| c != ' ').collect_vec();

        let head_idx = cs.iter().position(|&c| c == '<' || c == '>').ok_or(ParseConfigError::NoHead)?;
        let (dir, i1, i2, state_idx) = if cs[head_idx] == '<' {
            (TMDirection::Left, head_idx, head_idx+1, head_idx+1)
        } else {
            (TMDirection::Right, head_idx-1, head_idx, head_idx-1)
        };

        let state = State::from_str(&cs.get(state_idx)
                .ok_or(ParseConfigError::NoState)?
                .to_string())
            .map_err(|_| ParseConfigError::BadState)?;

        fn parse_symbol(c: &char) -> Result<GeneralSymbol, ParseConfigError> {
            if c.is_numeric() {
                Ok(GeneralSymbol::Basic(Symbol(
                    c.to_string().parse::<u8>().map_err(|_| ParseConfigError::BadSymbol)?)
                ))
            } else if *c == '^' || *c == '$' {
                Ok(GeneralSymbol::End)
            } else {
                Err(ParseConfigError::BadSymbol)
            }
        }

        let mut ltape = cs[..i1].iter().map(parse_symbol).collect::<Result<Vec<_>,_>>()?;
        let mut rtape = cs[i2+1..].iter().map(parse_symbol).rev().collect::<Result<Vec<_>,_>>()?;

        if enforce_end_wildcards {
            if ltape.len() == 0 || ltape[0] != GeneralSymbol::End {
                ltape.insert(0, GeneralSymbol::Wildcard);
            }
    
            if rtape.len() == 0 || rtape[0] != GeneralSymbol::End {
                rtape.insert(0, GeneralSymbol::Wildcard);
            }
        }

        Ok(Self {
            left_tape: ltape,
            right_tape: rtape,
            dir,
            state
        })
    }
}

impl FromStr for DirectedHeadConfig {
    type Err = ParseConfigError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::parse_str(s, true)
    }
}

impl fmt::Display for DirectedHeadConfig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for s in &self.left_tape {
            write!(f, "{}", s)?;
        }        

        match self.dir {
            TMDirection::Left => write!(f, " <{:?} ", self.state)?,
            TMDirection::Right => write!(f, " {:?}> ", self.state)?,
        }

        for s in (&self.right_tape).iter().rev() {
            write!(f, "{}", s)?;
        }

        Ok(())
    }
}

pub struct DirectedHeadSimulator<'a> {
    pub config: DirectedHeadConfig,
    tm: &'a TuringMachine,
    pub time: usize,
    undefined: bool,
    time_limit: usize,
}

#[derive(Debug, PartialEq)]
pub enum DirectedHeadStepResult {
    Success,
    Undefined,
    RanOffTape,
    OutOfTime
}

impl<'a> DirectedHeadSimulator<'a> {
    pub fn new(config: &DirectedHeadConfig, tm: &'a TuringMachine) -> Self {
        DirectedHeadSimulator {
            config: config.clone(),
            tm,
            time: 0,
            undefined: false,
            time_limit: 1000,
        }
    }

    pub fn step(&mut self) -> DirectedHeadStepResult {
        if self.undefined {
            return DirectedHeadStepResult::Undefined;
        }

        self.time += 1;

        let curr_symbol = {
            let tape = if self.config.dir == TMDirection::Left {
                &mut self.config.left_tape
            } else {
                &mut self.config.right_tape
            };
            match tape.pop() {
                Some(GeneralSymbol::Wildcard) => return DirectedHeadStepResult::RanOffTape,
                Some(GeneralSymbol::End) => {
                    tape.push(GeneralSymbol::End);
                    Symbol(0)
                },
                Some(GeneralSymbol::Basic(s)) => s,
                None => return DirectedHeadStepResult::RanOffTape,
            }
        };

        if let Some(transition) = &self.tm.transitions[self.config.state as usize][curr_symbol.0 as usize] {
            self.config.state = transition.new_state;
            self.config.dir = transition.direction;
            let tape = match transition.direction {
                TMDirection::Left => &mut self.config.right_tape,
                TMDirection::Right => &mut self.config.left_tape,
            };
            tape.push(GeneralSymbol::Basic(transition.new_symbol));

            if self.time > self.time_limit {
                DirectedHeadStepResult::OutOfTime
            } else {
                DirectedHeadStepResult::Success
            }
        } else {
            self.undefined = true;
            // technically the tape state here is inaccurate; would need to put that popped symbol back in
            DirectedHeadStepResult::Undefined
        }        
    }
}

pub fn reduce_config(config: &DirectedHeadConfig) -> DirectedHeadConfig {
    let mut config = config.clone();
    for tape in [&mut config.left_tape, &mut config.right_tape] {
        if tape.len() >= 1 && tape[0] == GeneralSymbol::End {
            while tape.len() >= 2 && tape[1] == GeneralSymbol::Basic(Symbol(0)) {
                tape.remove(1);
            }
        }
    }    
    config
}

pub fn run_to_undefined(starting_config: DirectedHeadConfig, tm: &TuringMachine, verbose: CheckerVerbosity) -> Result<usize, DirectedHeadStepResult> {
    let mut sim = DirectedHeadSimulator::new(&starting_config, tm);

    if verbose as isize >= 2 {
        println!();
    }
    if verbose as isize >= 1 {
        print!("{}: {} ", &sim.time, &sim.config);
    }
    if verbose as isize >= 2 {
        println!();
    }

    loop {
        let res = sim.step();
        
        if verbose as isize >= 2 {
            println!("{}: {} ", &sim.time, &sim.config);
        }
        
        if res == DirectedHeadStepResult::Undefined {
            if verbose as isize == 1 {
                println!("--> {}: {} Undefined", &sim.time, &sim.config);
            }
            return Ok(sim.time);
        } else if res != DirectedHeadStepResult::Success {
            if verbose as isize == 1 {
                println!("--> {}: {} ", &sim.time, &sim.config);
            }
            if verbose as isize >= 2 {
                println!("{:?}", res);
            }
            return Err(res);
        }
    }
}

#[derive(Clone, Copy)]
pub enum CheckerVerbosity {
    Off = 0,
    Some = 1,
    All = 2
}

pub fn check_transition_rule(rule: ConfigTransitionRule, tm: &TuringMachine, verbose: CheckerVerbosity) -> Result<usize, DirectedHeadStepResult> {
    let mut sim = DirectedHeadSimulator::new(&rule.before, tm);
    if verbose as isize >= 2 {
        println!();
    }
    if verbose as isize >= 1 {
        print!("{}: {} ", &sim.time, &sim.config);
    }
    if verbose as isize >= 2 {
        println!();
    }

    if sim.config == rule.after {
        if verbose as isize >= 1 {
            println!("{}: {} ", &sim.time, &sim.config);
        }
        return Ok(sim.time);
    } else if reduce_config(&sim.config) == reduce_config(&rule.after) {
        if verbose as isize >= 1 {
            println!("{}: {} ", &sim.time, &sim.config);
        }
        return Ok(sim.time);
    }
    
    loop {
        let res = sim.step();
        if verbose as isize >= 2 {
            println!("{}: {} ", &sim.time, &sim.config);
        }
        
        if res == DirectedHeadStepResult::Success {
            if sim.config == rule.after {
                if verbose as isize == 1 {
                    println!("--> {}: {} ", &sim.time, &sim.config);
                }
                return Ok(sim.time);
            } else if reduce_config(&sim.config) == reduce_config(&rule.after) {
                if verbose as isize == 1 {
                    println!("--> {}: {} ", &sim.time, &sim.config);
                }
                return Ok(sim.time);
            }
        } else {
            if verbose as isize == 1 {
                println!("--> {}: {} ", &sim.time, &sim.config);
            }
            if verbose as isize >= 2 {
                println!("{:?}", res);
            }
            return Err(res);
        }
    }
}

#[derive(Debug)]
pub struct RLEDefinitionSymbol {
    pub symbol: Symbol,
    pub repeat: bool
}

#[derive(Debug, PartialEq, Eq)]
pub struct ParseRLEDefinitionSymbolError;

impl FromStr for RLEDefinitionSymbol {
    type Err = ParseRLEDefinitionSymbolError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let repeat = s.ends_with("^n");
        let num_s = if repeat { &s[..s.len()-2] } else { s };
        let num = num_s.parse::<u8>().map_err(|_| ParseRLEDefinitionSymbolError)?;
        Ok(Self {
            symbol: Symbol(num),
            repeat
        })
    }
}

#[derive(Debug)]
pub struct RLEDefinition {
    pub left: Vec<RLEDefinitionSymbol>,
    pub right: Vec<RLEDefinitionSymbol>
}

impl RLEDefinition {
    pub fn new(left_def: &str, right_def: &str) -> Result<Self, ParseRLEDefinitionSymbolError> {
        Ok(Self {
            left: Self::parse_symbols(left_def)?,
            right: Self::parse_symbols(right_def)?,
        })
    }

    fn parse_symbols(s: &str) -> Result<Vec<RLEDefinitionSymbol>, ParseRLEDefinitionSymbolError> {
        s.split_whitespace()
            .map(|s2| s2.parse())
            .collect()
    }
}