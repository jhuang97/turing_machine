use std::env;
use std::fmt;
use std::fmt::format;
use std::fs;
use std::io::Write;
use std::rc::Rc;

use proc_macro2::Ident;
use proc_macro2::TokenStream;
use quote::format_ident;
use quote::quote;
use syn::token::Token;
use turing_machine::CheckerVerbosity;
use turing_machine::ConfigTransitionRule;
use turing_machine::DirectedHeadConfig;
use turing_machine::GeneralSymbol;
use turing_machine::ParseConfigError;
use turing_machine::RLEDefinition;
use turing_machine::RLEDefinitionSymbol;
use turing_machine::Symbol;
use turing_machine::TMDirection;
use turing_machine::TuringMachine;
use turing_machine::check_transition_rule;

fn process_tm_rle_file(
    fname: &str,
    verbosity: CheckerVerbosity,
) -> (
    String,
    TuringMachine,
    Vec<Rc<Metastate>>,
    Vec<Rc<SymbolOverRLE>>,
    Vec<CheckedRule>,
) {
    let contents = fs::read_to_string(fname).unwrap();
    let lines: Vec<String> = contents
        .lines()
        .filter(|s| s.len() > 0)
        .map(|s| s.to_owned())
        .collect();

    assert!(lines[0].starts_with("tm = "));
    let tm_def = &lines[0]["tm = ".len()..];
    let tm = TuringMachine::from_standard_notation(tm_def);

    let (section_indices, section_titles): (Vec<usize>, Vec<String>) = lines
        .iter()
        .enumerate()
        .filter(|(_, s)| s.starts_with("[") && s.ends_with("]"))
        .map(|(i, s)| (i, s[1..s.len() - 1].to_owned()))
        .unzip();
    let mut indices_end = section_indices[1..section_indices.len()].to_vec();
    indices_end.push(lines.len());
    let lines_by_section: Vec<_> = section_indices
        .iter()
        .zip(indices_end.iter())
        .map(|(i1, &i2)| &lines[i1 + 1..i2])
        .collect();

    // for (title, section_lines) in section_titles.iter().zip(lines_by_section.iter()) {
    //     println!("{title}");
    //     for line in section_lines.iter() {
    //         println!("----{line}");
    //     }
    // }

    assert!(section_titles[0] == "metastates");
    let state_table = parse_metastates(lines_by_section[0]).unwrap();

    for metastate in &state_table {
        println!(
            "{}, {}, {}",
            metastate.name, metastate.short_name, metastate.definition
        );
    }

    assert!(section_titles[1] == "rle");
    let rle_def = parse_rle_definition(lines_by_section[1]);

    assert!(section_titles[2] == "symbols over rle");
    let symbol_table = parse_symbol_definitions(lines_by_section[2]);

    assert!(section_titles[3] == "rules");
    let rules: Vec<PrototypeRule> = lines_by_section[3]
        .iter()
        .map(|s| parse_rule(s.as_str(), &state_table, &symbol_table))
        .collect::<Result<Vec<_>, _>>()
        .unwrap();
    let base_rules: Vec<ConfigTransitionRule> =
        rules.iter().map(|r| r.to_base_rule(&rle_def)).collect();

    let mut checked_rules = Vec::new();
    let mut n_verified = 0;
    let mut n_not_verified = 0;
    for (rule, base_rule) in rules.iter().zip(base_rules) {
        print!("{rule} ... ");
        let res = check_transition_rule(base_rule, &tm, verbosity);
        println!("{:?}", &res);
        match res {
            Ok(n_steps) => {
                n_verified += 1;
                checked_rules.push(CheckedRule {
                    before: rule.before.clone(),
                    after: rule.after.clone(),
                    n_steps,
                    original_input: rule.original_input.clone(),
                })
            }
            _ => n_not_verified += 1,
        }
    }

    println!("{n_verified} rule(s) verified, {n_not_verified} rule(s) not verified.\n");

    (
        tm_def.to_owned(),
        tm,
        state_table,
        symbol_table,
        checked_rules,
    )
}

#[derive(PartialEq)]
struct Metastate {
    name: String,
    short_name: String,
    definition: DirectedHeadConfig,
    original_def: String,
    ident: Ident,
}

fn parse_metastates(lines: &[String]) -> Result<Vec<Rc<Metastate>>, ParseConfigError> {
    let mut state_table = Vec::new();
    for line in lines {
        let parts: Vec<_> = line.split_whitespace().collect();
        assert!(parts.len() == 3);

        let config = DirectedHeadConfig::parse_str(&parts[2], false)?;
        state_table.push(Rc::new(Metastate {
            name: parts[0].to_owned(),
            short_name: parts[1].to_owned(),
            definition: config,
            original_def: parts[2].to_owned(),
            ident: format_ident!("{}", parts[0]),
        }));
    }
    Ok(state_table)
}

fn parse_rle_definition(lines: &[String]) -> RLEDefinition {
    let mut left_def: Option<&str> = None;
    let mut right_def: Option<&str> = None;
    for line in lines {
        let (part1, part2) = line.split_once(" = ").unwrap();
        if part1 == "left" {
            left_def = Some(part2);
        } else if part1 == "right" {
            right_def = Some(part2);
        } else {
            eprintln!("uh oh");
        }
    }
    RLEDefinition::new(left_def.unwrap(), right_def.unwrap()).unwrap()
}

fn parse_symbol_definitions(lines: &[String]) -> Vec<Rc<SymbolOverRLE>> {
    let mut symbol_table = Vec::new();
    for line in lines {
        let (name_s, definition_s) = line.split_once(" = ").unwrap();
        let (name, repeat): (String, bool) = if name_s.ends_with("(exp)") {
            (name_s[..name_s.len() - 5].to_owned(), true)
        } else {
            (name_s.to_owned(), false)
        };

        let definition = definition_s
            .chars()
            .map(|c| match c {
                '^' | '$' => MetaRLESymbol::End,
                '0'..='9' => MetaRLESymbol::Run(c.to_digit(10).unwrap().try_into().unwrap()),
                _ => unimplemented!(),
            })
            .collect::<Vec<_>>();
        symbol_table.push(Rc::new(SymbolOverRLE {
            name: name.clone(),
            definition,
            repeat,
            ident: format_ident!("{name}"),
        }));
    }
    symbol_table
}

#[derive(Debug)]
enum MetaRLESymbol {
    Run(u8),
    End,
}

#[derive(Debug)]
struct SymbolOverRLE {
    name: String,
    definition: Vec<MetaRLESymbol>,
    repeat: bool,
    ident: Ident,
}

impl fmt::Display for SymbolOverRLE {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        Ok(())
    }
}

#[derive(Clone)]
struct PrototypeConfig {
    lhs: Vec<Rc<SymbolOverRLE>>,
    rhs: Vec<Rc<SymbolOverRLE>>,
    metastate: Rc<Metastate>,
}

impl PrototypeConfig {
    fn to_base_config(&self, rle_def: &RLEDefinition) -> DirectedHeadConfig {
        fn extend(
            tape: &mut Vec<GeneralSymbol>,
            higher_symbol: Rc<SymbolOverRLE>,
            def: &Vec<RLEDefinitionSymbol>,
        ) {
            for symbol in &higher_symbol.definition {
                match *symbol {
                    MetaRLESymbol::Run(n) => {
                        for base_symbol in def {
                            if base_symbol.repeat {
                                for _ in 0..n {
                                    tape.push(GeneralSymbol::Basic(base_symbol.symbol));
                                }
                            } else {
                                tape.push(GeneralSymbol::Basic(base_symbol.symbol));
                            }
                        }
                    }
                    MetaRLESymbol::End => tape.push(GeneralSymbol::End),
                }
            }
        }

        let mut ltape: Vec<GeneralSymbol> = Vec::new();
        for symbol in &self.lhs {
            extend(&mut ltape, Rc::clone(symbol), &rle_def.left);
        }

        let mut rtape: Vec<GeneralSymbol> = Vec::new();
        for symbol in &self.rhs {
            extend(&mut rtape, Rc::clone(symbol), &rle_def.right);
        }

        rtape.reverse();

        let head_config = &self.metastate.definition;
        ltape.extend(&head_config.left_tape);
        rtape.extend(&head_config.right_tape);

        if ltape.len() == 0 || ltape[0] != GeneralSymbol::End {
            ltape.insert(0, GeneralSymbol::Wildcard);
        }

        if rtape.len() == 0 || rtape[0] != GeneralSymbol::End {
            rtape.insert(0, GeneralSymbol::Wildcard);
        }

        DirectedHeadConfig {
            left_tape: ltape,
            right_tape: rtape,
            dir: head_config.dir,
            state: head_config.state,
        }
    }
}

impl fmt::Display for PrototypeConfig {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if !self.lhs.is_empty() {
            for s in &self.lhs {
                write!(f, "{} ", s)?;
            }
        }
        write!(f, "{}", self.metastate.short_name)?;
        if !self.rhs.is_empty() {
            for s in &self.rhs {
                write!(f, " {}", s)?;
            }
        }
        Ok(())
    }
}

struct PrototypeRule {
    before: PrototypeConfig,
    after: PrototypeConfig,
    original_input: String,
}

impl fmt::Display for PrototypeRule {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{} -> {}", self.before, self.after)
    }
}

impl PrototypeRule {
    fn to_base_rule(&self, rle_def: &RLEDefinition) -> ConfigTransitionRule {
        ConfigTransitionRule {
            before: self.before.to_base_config(rle_def),
            after: self.after.to_base_config(rle_def),
        }
    }
}

struct CheckedRule {
    before: PrototypeConfig,
    after: PrototypeConfig,
    n_steps: usize,
    original_input: String,
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseRuleError {
    SymbolNotFound,
    Split,
}

fn parse_rule(
    s: &str,
    state_table: &Vec<Rc<Metastate>>,
    symbol_table: &Vec<Rc<SymbolOverRLE>>,
) -> Result<PrototypeRule, ParseRuleError> {
    let (before_s, after_s) = s.split_once("->").ok_or(ParseRuleError::Split)?;
    let before = parse_config(before_s, state_table, symbol_table)?;
    let after = parse_config(after_s, state_table, symbol_table)?;
    Ok(PrototypeRule {
        before,
        after,
        original_input: s.to_owned(),
    })
}

fn parse_config(
    s: &str,
    state_table: &Vec<Rc<Metastate>>,
    symbol_table: &Vec<Rc<SymbolOverRLE>>,
) -> Result<PrototypeConfig, ParseRuleError> {
    let (left_s, right_s, state) = split_rule(s, state_table)?;
    let lhs = left_s
        .trim()
        .split_whitespace()
        .map(|s| parse_higher_symbol(s, symbol_table))
        .collect::<Result<Vec<_>, _>>()?;
    let rhs = right_s
        .trim()
        .split_whitespace()
        .map(|s| parse_higher_symbol(s, symbol_table))
        .collect::<Result<Vec<_>, _>>()?;

    Ok(PrototypeConfig {
        lhs,
        rhs,
        metastate: state,
    })
}

fn split_rule(
    s: &str,
    state_table: &Vec<Rc<Metastate>>,
) -> Result<(String, String, Rc<Metastate>), ParseRuleError> {
    for state in state_table {
        let delim = if s.starts_with(&state.short_name) {
            format!("{} ", state.short_name)
        } else if s.ends_with(&state.short_name) {
            format!(" {}", state.short_name)
        } else {
            format!(" {} ", state.short_name)
        };
        if s.contains(&delim) {
            let (left, right) = s.split_once(&delim).ok_or(ParseRuleError::Split)?;
            return Ok((left.to_owned(), right.to_owned(), Rc::clone(state)));
        }
    }
    Err(ParseRuleError::Split)
}

fn parse_higher_symbol(
    s: &str,
    symbol_table: &Vec<Rc<SymbolOverRLE>>,
) -> Result<Rc<SymbolOverRLE>, ParseRuleError> {
    for symbol in symbol_table {
        if s == symbol.name {
            return Ok(Rc::clone(symbol));
        }
    }
    eprintln!("Cannot parse symbol {s}");
    Err(ParseRuleError::SymbolNotFound)
}

struct RuleImpl {
    left_match: TokenStream,
    right_match: TokenStream,
    sim_changes: TokenStream,
    step_count: TokenStream,
}

/// all tape slices are ordered from further-from-head to nearest-to-head
/// most general rightward rule: [LI] > [RI] Y^n -> X^n [LI] > [RI]
/// most general leftward rule: X^n [LI] < [RI] -> [LI] < [RI] Y^n
/// the "from" half-tape should lose one RLE symbol
/// the "to" half-tape should gain one RLE symbol
fn directionless_pass_through(
    from0: &[Rc<SymbolOverRLE>],
    from1: &[Rc<SymbolOverRLE>],
    from_ident: Ident,
    to0: &[Rc<SymbolOverRLE>],
    to1: &[Rc<SymbolOverRLE>],
    to_ident: Ident,
) -> Option<(TokenStream, TokenStream, TokenStream)> {
    if from0.len() != from1.len() + 1 {
        return None;
    }
    if to0.len() + 1 != to1.len() {
        return None;
    }

    // the symbol coming in and the symbol going out should both be run length-encoded
    if !from0[0].repeat || !to1[0].repeat {
        return None;
    }

    // the block must not have other RLE symbols; the blocks must match
    let cannot_match_preserved_block = |(s1, s2): (&Rc<SymbolOverRLE>, &Rc<SymbolOverRLE>)| {
        s1.repeat || s2.repeat || s1.name != s2.name
    };
    if (&to0[..])
        .iter()
        .zip((&to1[1..]).iter())
        .any(cannot_match_preserved_block)
    {
        return None;
    }
    if (&from0[1..])
        .iter()
        .zip((&from1[..]).iter())
        .any(cannot_match_preserved_block)
    {
        return None;
    }

    let from_symbol = Rc::clone(&from0[0]);
    let to_symbol = Rc::clone(&to1[0]);
    let from_block = from1.to_vec();
    let to_block = to0.to_vec();

    let from_symb_ident = &from_symbol.ident;
    let to_symb_ident = &to_symbol.ident;
    let from_symb_expr = quote! { Run(#from_symb_ident, exp) };
    let block_idents = (&from0[1..]).iter().map(|s| {
        let ident = s.ident.clone();
        quote! { #ident }
    });
    let from_match = quote! { [.., #from_symb_expr, #(#block_idents),*]};
    let to_match = half_tape_match(&to_block);

    let mut changes_vec: Vec<TokenStream> = vec![quote! { let n = *exp; }];
    for _ in 0..from0.len() {
        changes_vec.push(quote! { self.#from_ident.pop(); });
    }
    for s in &from_block {
        let s_ident = s.ident.clone();
        changes_vec.push(quote! { self.#from_ident.push(#s_ident); });
    }

    for _ in 0..to_block.len() {
        changes_vec.push(quote! { self.#to_ident.pop(); });
    }
    changes_vec.push(quote! { add_or_merge_run(&mut self.#to_ident, #to_symb_ident, n); });
    for s in &to_block {
        let s_ident = s.ident.clone();
        changes_vec.push(quote! { self.#to_ident.push(#s_ident); });
    }

    Some((from_match, to_match, quote! { #(#changes_vec)* }))
}

fn try_process_passing_through_run(rule: &CheckedRule) -> Option<RuleImpl> {
    let state0 = &rule.before.metastate;
    let state1 = &rule.after.metastate;
    if state0 != state1 {
        return None;
    }

    let left0 = &rule.before.lhs;
    let left1 = &rule.after.lhs;
    let right0: Vec<_> = rule.before.rhs.iter().rev().map(|s| Rc::clone(s)).collect();
    let right1: Vec<_> = rule.after.rhs.iter().rev().map(|s| Rc::clone(s)).collect();

    let (left_match, right_match, sim_changes) = if let Some(res) = directionless_pass_through(
        &right0,
        &right1,
        format_ident!("right_tape"),
        &left0,
        &left1,
        format_ident!("left_tape"),
    ) {
        (res.1, res.0, res.2)
    } else if let Some(res) = directionless_pass_through(
        &left0,
        &left1,
        format_ident!("left_tape"),
        &right0,
        &right1,
        format_ident!("right_tape"),
    ) {
        res
    } else {
        return None;
    };

    let rule_steps = rule.n_steps as u128;
    let step_count = quote! { #rule_steps * n };

    Some(RuleImpl {
        left_match,
        right_match,
        sim_changes,
        step_count,
    })
}

fn half_tape_match(half_tape0: &Vec<Rc<SymbolOverRLE>>) -> TokenStream {
    if half_tape0.is_empty() {
        return quote! { _ };
    }

    let symbols_match = half_tape0.iter().enumerate().map(|(idx, s)| {
        let ident = s.ident.clone();
        if s.repeat {
            if idx == 0 {
                quote! { Run(#ident, _) }
            } else {
                quote! { Run(#ident, 1) }
            }
        } else {
            quote! { #ident }
        }
    });

    quote! { [.., #(#symbols_match),*]}
}

enum TapeAddition {
    Run { symb: Rc<SymbolOverRLE>, exp: u128 },
    Normal(Rc<SymbolOverRLE>),
}

fn half_tape_changes(
    half_tape0: &Vec<Rc<SymbolOverRLE>>,
    half_tape_new: &Vec<Rc<SymbolOverRLE>>,
    tape_ident: Ident,
) -> Vec<TokenStream> {
    let mut change_start_idx = 0;
    while half_tape0.len() > change_start_idx
        && half_tape_new.len() > change_start_idx
        && half_tape0[change_start_idx].name == half_tape_new[change_start_idx].name
    {
        change_start_idx += 1;
    }

    let mut changes = Vec::new();

    // remove old symbols from half tape
    for idx in (change_start_idx..half_tape0.len()).rev() {
        changes.push(if idx == 0 && half_tape0[0].repeat {
            let t = half_tape0[0].ident.clone();
            quote! { decrement_run(&mut self.#tape_ident, #t); }
        } else {
            quote! { self.#tape_ident.pop(); }
        });
    }

    use TapeAddition::*;

    // add new symbols to half tape
    let mut additions: Vec<_> = half_tape_new[change_start_idx..]
        .to_vec()
        .chunk_by(|a, b| a.repeat && b.repeat && a.name == b.name)
        .map(|s| {
            let s0 = s.first().unwrap();
            if s0.repeat {
                Run {
                    symb: Rc::clone(s0),
                    exp: s.len() as u128,
                }
            } else {
                assert_eq!(s.len(), 1);
                Normal(Rc::clone(s0))
            }
        })
        .enumerate()
        .map(|(tidx, tadd)| match tadd {
            Run { symb, exp } => {
                let t = symb.ident.clone();
                if change_start_idx == 0 && tidx == 0 {
                    quote! { add_or_merge_run(&mut self.#tape_ident, #t, #exp); }
                } else {
                    quote! { self.#tape_ident.push(Run(#t, #exp)); }
                }
            }
            Normal(symb) => {
                let t = symb.ident.clone();
                quote! { self.#tape_ident.push(#t); }
            }
        })
        .collect();

    changes.append(&mut additions);
    changes
}

fn try_process_rule_general(rule: &CheckedRule) -> Option<RuleImpl> {
    let state0 = &rule.before.metastate;
    let state1 = &rule.after.metastate;

    let mut changes_vec: Vec<TokenStream> = Vec::new();
    if state0 != state1 {
        let state_new = state1.ident.clone();
        changes_vec.push(quote! {
            self.state = #state_new;
        });
    }

    let lhs0 = &rule.before.lhs;
    let rtape0: Vec<_> = rule.before.rhs.iter().rev().map(|s| Rc::clone(s)).collect();

    let lhs1 = &rule.after.lhs;
    let rtape1: Vec<_> = rule.after.rhs.iter().rev().map(|s| Rc::clone(s)).collect();

    let left_match = half_tape_match(lhs0);
    let right_match = half_tape_match(&rtape0);
    changes_vec.extend(half_tape_changes(lhs0, lhs1, format_ident!("left_tape")));
    changes_vec.extend(half_tape_changes(
        &rtape0,
        &rtape1,
        format_ident!("right_tape"),
    ));

    let sim_changes = quote! { #(#changes_vec)* };
    let rule_steps = rule.n_steps as u128;

    Some(RuleImpl {
        left_match,
        right_match,
        sim_changes,
        step_count: quote! { #rule_steps },
    })
}

fn generate_rule_code(
    rule: &CheckedRule,
    symbol_table: &Vec<Rc<SymbolOverRLE>>,
    state_table: &Vec<Rc<Metastate>>,
) -> TokenStream {
    let case_comment = format!("\\ {}", rule.original_input);

    let state0_ident = &rule.before.metastate.ident.clone();

    let rule_impl: Option<RuleImpl> =
        try_process_passing_through_run(rule).or_else(|| try_process_rule_general(rule));

    if let Some(RuleImpl {
        left_match,
        right_match,
        sim_changes,
        step_count,
    }) = rule_impl
    {
        quote! {
            #[doc = #case_comment]
            (#state0_ident, #left_match, #right_match) => {
                #sim_changes
                #step_count
            }
        }
    } else {
        quote! {
            #[doc = #case_comment]
            (#state0_ident, _, _) => {
                #[doc = "oh no"]
                0
            }
        }
    }
}

fn generate_simulator_code(
    tm_def: String,
    state_table: Vec<Rc<Metastate>>,
    symbol_table: Vec<Rc<SymbolOverRLE>>,
    checked_rules: Vec<CheckedRule>,
) {
    let state_names = state_table.iter().map(|st| st.ident.clone());

    let state_print_cases = state_table.iter().map(|st| {
        let ident = st.ident.clone();
        let short_name = st.short_name.clone();
        quote! {
            HigherState::#ident => write!(f, "{}", #short_name.red().bold())?
        }
    });

    let non_run_symbol_names = symbol_table
        .iter()
        .filter(|st| !st.repeat)
        .map(|st| st.ident.clone());

    let run_symbol_names = symbol_table
        .iter()
        .filter(|st| st.repeat)
        .map(|st| st.ident.clone());

    let state_def = quote! {
        #[derive(Debug, PartialEq, Eq)]
        enum HigherState {
            #(#state_names),*
        }
    };

    let symbol_def = quote! {
        #[derive(Debug, Default, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
        enum RunSymbolType {
            #[default]
            #(#run_symbol_names),*
        }
        #[derive(Debug, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
        enum BlockSymbol {
            Run(RunSymbolType, Exp),
            #(#non_run_symbol_names),*
        }
    };

    let type_def = quote! {
        use strum_macros::EnumString;
        use std::fmt;
        const TM_DEF: &str = #tm_def;

        #[derive(Debug, Clone)]
        pub enum SimError {
            Halted,
            UndefinedTransition,
            Overflow
        }

        impl fmt::Display for SimError {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                match self {
                    Self::Halted => write!(f, "Halted"),
                    Self::UndefinedTransition => write!(f, "Undefined transition"),
                    Self::Overflow => write!(f, "Overflow"),
                }
            }
        }
    };

    let match_cases = checked_rules
        .iter()
        .map(|r| generate_rule_code(r, &symbol_table, &state_table));

    let block_sim_def = quote! {
        fn add_or_merge_run(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType, nadd: Exp) {
            use BlockSymbol::*;
            match tape.last_mut() {
                Some(Run(t, n)) if *t == run_type => *n += nadd,
                _ => tape.push(Run(run_type, nadd))
            }
        }

        fn decrement_run(tape: &mut Vec<BlockSymbol>, run_type: RunSymbolType) {
            use BlockSymbol::*;
            match tape.last_mut() {
                Some(Run(t, 1)) if *t == run_type => { tape.pop(); },
                Some(Run(t, n @ 2..)) if *t == run_type => *n -= 1,
                _ => unreachable!("expected at least one of run symbol")
            }
        }

        impl BlockSimulator {
            fn basic_step(&mut self) -> Result<Exp, SimError> {
                use HigherState::*;
                use BlockSymbol::*;
                use RunSymbolType::*;

                let n_steps = match (&self.state,
                    self.left_tape.as_slice(),
                    self.right_tape.as_slice(),) {
                    #(#match_cases)*
                    _ => return Err(SimError::UndefinedTransition),
                };
                Ok(n_steps)
            }
        }

        impl fmt::Display for BlockSimulator {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                use colored::*;

                const LEFT_PRINT_THRESHOLD: usize = 100;
                let l_th = LEFT_PRINT_THRESHOLD / 2;

                self.self_steps.fmt(f)?;
                write!(f, " | {}: ", self.base_steps)?;
                if self.left_tape.len() <= LEFT_PRINT_THRESHOLD {
                    for symb in &self.left_tape {
                        write!(f, "{} ", symb)?;
                    }
                } else {
                    for symb in &self.left_tape[..l_th] {
                        write!(f, "{} ", symb)?;
                    }
                    write!(f, " ...{} terms... ", self.left_tape.len() - LEFT_PRINT_THRESHOLD)?;
                    for symb in &self.left_tape[self.left_tape.len() - l_th..] {
                        write!(f, "{} ", symb)?;
                    }
                }
                match self.state {
                    #(#state_print_cases),*
                }

                const RIGHT_PRINT_THRESHOLD: usize = 200;
                let r_th = RIGHT_PRINT_THRESHOLD / 2;
                if self.right_tape.len() <= RIGHT_PRINT_THRESHOLD {
                    for symb in self.right_tape.iter().rev() {
                        write!(f, " {}", symb)?;
                    }
                } else {
                    for symb in self.right_tape[self.right_tape.len() - r_th..].iter().rev() {
                        write!(f, " {}", symb)?;
                    }
                    write!(f, " ...{} terms... ", self.right_tape.len() - RIGHT_PRINT_THRESHOLD)?;
                    for symb in self.right_tape[..r_th].iter().rev() {
                        write!(f, " {}", symb)?;
                    }
                }

                Ok(())
            }
        }
    };

    let code1 = quote! {
        #type_def
        #state_def
        #symbol_def
        #block_sim_def
    };

    let code2 = quote! {
        type Exp = u128;

        struct BlockSimulator {
            pub left_tape: Vec<BlockSymbol>,
            pub right_tape: Vec<BlockSymbol>,
            pub state: HigherState,
            pub base_steps: u128,
            pub self_steps: u64,
        }

        impl fmt::Display for BlockSymbol {
            fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
                use BlockSymbol::*;

                let s0 = match *self {
                    Run(t, _) => &format!("{:?}", t),
                    _ => &format!("{:?}", self),
                };

                let s_exp = match *self {
                    Run(_, n) => {
                        if n == 1 { "" }
                        else { &format!("^{}", n)}
                    },
                    _ => "",
                };
                write!(f, "{}{}", s0, s_exp)
            }
        }
    };

    let syntax_tree1 = syn::parse2(code1).unwrap();
    let formatted1 = prettyplease::unparse(&syntax_tree1).replace(r"///\", "//");
    let mut file1 = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .truncate(true)
        .open("higher_rule_generated_code_part1.txt")
        .unwrap();
    file1
        .write_all(
            format!("// Start of autogenerated code\n{formatted1}\n// End of autogenerated code")
                .as_bytes(),
        )
        .unwrap();

    let syntax_tree2 = syn::parse2(code2).unwrap();
    let formatted2 = prettyplease::unparse(&syntax_tree2);
    let mut file2 = fs::OpenOptions::new()
        .read(true)
        .write(true)
        .truncate(true)
        .open("higher_rule_generated_code_part2.txt")
        .unwrap();
    file2
        .write_all(
            format!("// Start of customizable code\n{formatted2}\n// End of customizable code")
                .as_bytes(),
        )
        .unwrap();
}

fn main() {
    // let fname = "src/definitions/bb6_tm_4_counter.txt";
    // let fname = "src/definitions/bb6_sk1like_1.txt";
    // let fname = "src/definitions/bb6_sk1like_2.txt";
    // let fname = "src/definitions/bb6_sk1like_nice.txt";
    let fname = "src/definitions/skelet1/skelet1_reimpl.txt";

    let (tm_def, tm, state_table, symbol_table, checked_rules) =
        process_tm_rle_file(fname, CheckerVerbosity::All);
    generate_simulator_code(tm_def, state_table, symbol_table, checked_rules);
}
