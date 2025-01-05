use core::str;
use std::fmt;
use std::str::FromStr;
use std::collections::VecDeque;
use strum_macros::EnumString;

#[derive(Debug)]
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

#[derive(Debug)]
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

#[derive(Debug, PartialEq, EnumString, Copy, Clone)]
pub enum TMDirection {
    #[strum(serialize = "L")]
    Left,
    #[strum(serialize = "R")]
    Right
}

#[derive(Debug, PartialEq, EnumString, Copy, Clone)]
pub enum State {
    A = 0,
    B = 1,
    C = 2,
    D = 3,
    E = 4,
}

const STATES: [State; 5] = [State::A, State::B, State::C, State::D, State::E];

pub struct BasicSimulator {
    tm: TuringMachine,
    pub tape: VecDeque<Symbol>,
    pub state: State,
    pub position: usize,
    pub time: usize,
    pub halted: bool,
    pub prev_dir: Option<TMDirection>,
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
            prev_dir: None
        }
    }

    pub fn step(&mut self) -> bool {
        if self.halted {
            return true;
        }

        self.time += 1;
        let cell = self.tape.get_mut(self.position).unwrap();

        if let Some(transition) = &self.tm.transitions[self.state as usize][cell.0 as usize] {
            *cell = transition.new_symbol;
            self.state = transition.new_state;
            match transition.direction {
                TMDirection::Left => {
                    if self.position == 0 {
                        self.tape.push_front(Symbol(0));
                    } else {
                        self.position -= 1;
                    }
                },
                TMDirection::Right => {
                    if self.position == self.tape.len()-1 {
                        self.tape.push_back(Symbol(0));
                    }
                    self.position += 1;
                }
            }
            self.prev_dir = Some(transition.direction);

            false
        } else {
            self.halted = true;
            true
        }
    }

    pub fn display_directed_head(&self) -> impl fmt::Display + '_ {
        DirectedHead(self)
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