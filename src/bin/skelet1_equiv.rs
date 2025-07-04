use std::env;
use std::str::FromStr;

use turing_machine::{check_transition_rule, skelet1_basic, CheckerVerbosity, ConfigTransitionRule, TuringMachine};
use turing_machine::skelet1_basic::{SKELET_1, is_skelet1_basic_state};

fn check_skelet1_config_transition_rules() {
    let rules_txt = include_str!("../definitions/skelet1/config_transition_rules.txt");
    let lines = rules_txt.lines().filter(|s| s.len() > 1);
    for line in lines {
        // let tm = TuringMachine::from_standard_notation(SKELET_1);
        let tm = TuringMachine::from_standard_notation("1RB0LF_1LC0RC_1RA1LD_0RE0LB_---1RC_1RD1RF");
        let rule = ConfigTransitionRule::from_str(line).unwrap();

        let res = check_transition_rule(rule, &tm, CheckerVerbosity::All);
        print!("{line}");
        match res {
            Ok(n_steps) => println!(" --- {n_steps} step(s)"),
            Err(err) => println!(" {err:?}"),
        }
    }
}

fn main() {
    // dbg!(TuringMachine::from_standard_notation(SKELET_1));
    // let tm = TuringMachine::from_standard_notation(SKELET_1);

    let candidates: &str = include_str!("../../bb6_skelet1_equiv_candidates.txt").trim();
    // let candidates: &str = include_str!("../../bb6_Sk1-like.txt").trim();
    // skelet1_basic::try_match_skelet1_basic_states(candidates, false);
    // skelet1_basic::try_match_skelet1_basic_states_candidate_7();
    skelet1_basic::try_match_skelet1_basic_states_alt(candidates, true);

    // let tm = TuringMachine::from_standard_notation(SKELET_1);
    // let rule = ConfigTransitionRule::from_str("011 <C10  ->  <C10  110").unwrap();

    // let tm = TuringMachine::from_standard_notation("1RB0LF_1LC0RC_1RA1LD_0RE0LB_---1RC_1RD1RF");
    // let rule = ConfigTransitionRule::from_str("1 A> 110 110  -> 1 011 011  A>").unwrap();
    // dbg!(check_transition_rule(rule, &tm, true));

    // check_skelet1_config_transition_rules();
}