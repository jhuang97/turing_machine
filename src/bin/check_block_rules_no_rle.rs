use std::env;
use std::fs;
use std::io::Write;
use std::rc::Rc;
use std::fmt;

use proc_macro2::Ident;
use proc_macro2::TokenStream;
use quote::format_ident;
use quote::quote;
use turing_machine::check_transition_rule;
use turing_machine::CheckerVerbosity;
use turing_machine::GeneralSymbol;
use turing_machine::Symbol;
use turing_machine::{TuringMachine, DirectedHeadConfig, ParseConfigError, ConfigTransitionRule};

fn process_tm_block_file(fname: &str) -> (String, TuringMachine, Vec<Rc<Metastate>>, Vec<Rc<Block>>, Vec<CheckedRule>) {
    let contents = fs::read_to_string(fname).unwrap();

    let lines: Vec<String> = contents.lines()
        .filter(|s| s.len() > 0)
        .map(|s| s.to_owned()).collect();

    assert!(lines[0].starts_with("tm = "));
    let tm_def = &lines[0]["tm = ".len()..];
    let tm = TuringMachine::from_standard_notation(tm_def);

    let (section_indices, section_titles): (Vec<usize>, Vec<String>) = lines.iter().enumerate()
        .filter(|(_, s)| s.starts_with("[") && s.ends_with("]"))
        .map(|(i, s)| (i, s[1..s.len()-1].to_owned()))
        .unzip();
    let mut indices_end = section_indices[1..section_indices.len()].to_vec();
    indices_end.push(lines.len());
    let lines_by_section: Vec<_> = section_indices.iter().zip(indices_end.iter()).map(|(i1, &i2)| &lines[i1+1..i2]).collect();

    // for (title, section_lines) in section_titles.iter().zip(lines_by_section.iter()) {
    //     println!("{title}");
    //     for line in section_lines.iter() {
    //         println!("----{line}");
    //     }
    // }

    assert!(section_titles[0] == "metastates");
    let state_table = parse_metastates(lines_by_section[0]).unwrap();

    for metastate in &state_table {
        println!("{}, {}, {}", metastate.name, metastate.short_name, metastate.definition);
    }

    assert!(section_titles[1] == "blocks");
    let block_table = parse_block_definitions(lines_by_section[1]);

    assert!(section_titles[2] == "rules");
    let rules: Vec<PrototypeRule> = lines_by_section[2].iter().map(|s| parse_rule(s.as_str(), &state_table, &block_table))
        .collect::<Result<Vec<_>,_>>().unwrap();
    let base_rules: Vec<ConfigTransitionRule> = rules.iter().map(|r| r.to_base_rule()).collect();

    let mut checked_rules = Vec::new();
    let mut n_verified = 0;
    let mut n_not_verified = 0;
    for (rule, base_rule) in rules.iter().zip(base_rules) {
        print!("{rule} ... ");
        let res = check_transition_rule(base_rule, &tm, CheckerVerbosity::All);
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
            },
            _ => n_not_verified += 1,
        }
    }

    println!("{n_verified} rule(s) verified, {n_not_verified} rule(s) not verified.\n");

    (tm_def.to_owned(), tm, state_table, block_table, checked_rules)
}

#[derive(PartialEq)]
struct Metastate {
    name: String,
    short_name: String,
    definition: DirectedHeadConfig,
    ident: Ident
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
            ident: format_ident!("{}", parts[0])
        }));
    }
    Ok(state_table)
}

#[derive(Debug)]
enum BlockDefSymbol {
    Basic(u8),
    End
}

#[derive(Debug)]
struct Block {
    name: String,
    definition: Vec<BlockDefSymbol>,
    ident: Ident
}

impl fmt::Display for Block {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        Ok(())
    }
}

fn parse_block_definitions(lines: &[String]) -> Vec<Rc<Block>> {
    let mut block_table = Vec::new();
    for line in lines {
        let (name, definition_s) = line.split_once(" = ").unwrap();

        let definition = definition_s.chars()
            .map(|c| match c {
                '^' | '$' => BlockDefSymbol::End,
                '0'..='9' => BlockDefSymbol::Basic(c.to_digit(10).unwrap().try_into().unwrap()),
                _ => unimplemented!()
            })
            .collect::<Vec<_>>();
        block_table.push(Rc::new(Block { 
            name: name.to_owned(), 
            definition,
            ident: format_ident!("{name}")
        }));
    }
    block_table
}

#[derive(Clone)]
struct PrototypeConfig {
    lhs: Vec<Rc<Block>>,
    rhs: Vec<Rc<Block>>,
    metastate: Rc<Metastate>,
}

impl PrototypeConfig {
    fn to_base_config(&self) -> DirectedHeadConfig {
        fn extend(tape: &mut Vec<GeneralSymbol>, higher_symbol: Rc<Block>) {
            for symbol in &higher_symbol.definition {
                match *symbol {
                    BlockDefSymbol::Basic(n) => tape.push(GeneralSymbol::Basic(Symbol(n))),
                    BlockDefSymbol::End => tape.push(GeneralSymbol::End),
                }
            }
        }

        let mut ltape: Vec<GeneralSymbol> = Vec::new();
        for symbol in &self.lhs {
            extend(&mut ltape, Rc::clone(symbol));
        }

        let mut rtape: Vec<GeneralSymbol> = Vec::new();
        for symbol in &self.rhs {
            extend(&mut rtape, Rc::clone(symbol));
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
    fn fmt (&self, f: &mut fmt::Formatter) -> fmt::Result {
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
    fn to_base_rule(&self) -> ConfigTransitionRule {
        ConfigTransitionRule {
            before: self.before.to_base_config(),
            after: self.after.to_base_config()
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum ParseRuleError {
    SymbolNotFound,
    Split
}

fn parse_rule(s: &str, state_table: &Vec<Rc<Metastate>>, 
    block_table: &Vec<Rc<Block>>) -> Result<PrototypeRule, ParseRuleError>
{
    let (before_s, after_s) = s.split_once("->").ok_or(ParseRuleError::Split)?;
    let before = parse_config(before_s, state_table, block_table)?;
    let after = parse_config(after_s, state_table, block_table)?;
    Ok(PrototypeRule { before, after, original_input: s.to_owned() })
}

fn parse_config(s: &str, state_table: &Vec<Rc<Metastate>>, 
    block_table: &Vec<Rc<Block>>) -> Result<PrototypeConfig, ParseRuleError>
{
    let (left_s, right_s, state) = split_rule(s, state_table)?;
    let lhs = left_s.trim().split_whitespace()
        .map(|s| parse_block(s, block_table))
        .collect::<Result<Vec<_>,_>>()?;
    let rhs = right_s.trim().split_whitespace()
        .map(|s| parse_block(s, block_table))
        .collect::<Result<Vec<_>,_>>()?;

    Ok(PrototypeConfig { lhs, rhs, metastate: state })
}

fn split_rule(s: &str, state_table: &Vec<Rc<Metastate>>) -> Result<(String, String, Rc<Metastate>), ParseRuleError> {
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

fn parse_block(s: &str, block_table: &Vec<Rc<Block>>) -> Result<Rc<Block>, ParseRuleError> {
    for block in block_table {
        if s == block.name {
            return Ok(Rc::clone(block))
        }
    }
    Err(ParseRuleError::SymbolNotFound)
}

struct CheckedRule {
    before: PrototypeConfig,
    after: PrototypeConfig,
    n_steps: usize,
    original_input: String
}

struct RuleImpl {
    left_match: TokenStream,
    right_match: TokenStream,
    sim_changes: TokenStream,
    step_count: TokenStream,
}

fn half_tape_match(half_tape0: &Vec<Rc<Block>>) -> TokenStream {
    if half_tape0.is_empty() {
        return quote! { _ };
    }

    let symbols_match = half_tape0.iter().enumerate().map(|(idx, s)| {
        let ident = s.ident.clone();
        quote! { #ident }
    });

    quote!{ [.., #(#symbols_match),*]}
}

fn half_tape_changes(half_tape0: &Vec<Rc<Block>>, half_tape_new: &Vec<Rc<Block>>,
    tape_ident: Ident
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
        changes.push( quote! { self.#tape_ident.pop(); } );
    }

    // add new symbols to half tape
    for idx in change_start_idx..half_tape_new.len() {
        let t = half_tape_new[idx].ident.clone();
        changes.push( quote! { self.#tape_ident.push(#t); } );
    }

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
    let rtape0: Vec<_> = rule.before.rhs.iter()
        .rev()
        .map(|s| Rc::clone(s)).collect();

    let lhs1 = &rule.after.lhs;
    let rtape1: Vec<_> = rule.after.rhs.iter()
        .rev()
        .map(|s| Rc::clone(s)).collect();

    let left_match = half_tape_match(lhs0);
    let right_match = half_tape_match(&rtape0);
    changes_vec.extend(half_tape_changes(lhs0, lhs1, format_ident!("left_tape")));
    changes_vec.extend(half_tape_changes(&rtape0, &rtape1, format_ident!("right_tape")));

    let sim_changes = quote! { #(#changes_vec)* };
    let rule_steps = rule.n_steps as u128;

    Some(RuleImpl {
        left_match, right_match, sim_changes,
        step_count: quote! { #rule_steps }
    })
}

fn generate_rule_code(rule: &CheckedRule, symbol_table: &Vec<Rc<Block>>, state_table: &Vec<Rc<Metastate>>) -> TokenStream {
    let case_comment = format!(" {}", rule.original_input);

    let state0_ident = &rule.before.metastate.ident.clone();

    let rule_impl: Option<RuleImpl> = try_process_rule_general(rule);

    if let Some(RuleImpl {left_match, right_match, sim_changes, step_count}) = rule_impl {
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

fn main() {
    let (tm_def, tm, state_table, block_table, checked_rules) = 
        process_tm_block_file("src/definitions/bb25_family_0LB.txt");

    let state_names = state_table.iter()
        .map(|st| st.ident.clone());

    let state_print_cases = state_table.iter()
        .map(|st| {
            let ident = st.ident.clone();
            let short_name = st.short_name.clone();
            quote! {
                HigherState::#ident => write!(f, "{}", #short_name.red().bold())?
            }
        });

    let block_names = block_table.iter().map(|st| st.ident.clone());

    let state_def = quote! {
        #[derive(PartialEq, Eq, Copy, Clone)]
        enum HigherState {
            #(#state_names),*
        }
    };

    let block_def = quote! {
        #[derive(Debug, PartialEq, EnumString, Copy, Clone, Eq, Hash)]
        enum BlockSymbol {
            #(#block_names),*
        }
    };

    let type_def = quote! {
        use strum_macros::EnumString;
        use std::fmt;
        use turing_machine::TuringMachine;
        const TM_DEF: &str = #tm_def;

        #[derive(Debug, Clone)]
        pub enum SimError {
            Halted,
            UndefinedTransition,
        }

        impl fmt::Display for SimError {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                match self {
                    Self::Halted => write!(f, "Halted"),
                    Self::UndefinedTransition => write!(f, "Undefined transition")
                }
            }
        }
    };

    let match_cases = checked_rules.iter().map(|r| generate_rule_code(r, &block_table, &state_table));

    let block_sim_def = quote! {
        impl BlockSimulator {
            fn basic_step(&mut self) -> Result<Exp, SimError> {
                use HigherState::*;
                use BlockSymbol::*;

                let n_steps = match (&self.state,
                    self.left_tape.as_slice(),
                    self.right_tape.as_slice(),) {
                    #(#match_cases)*
                    _ => return Err(SimError::UndefinedTransition),
                };
                Ok(n_steps)
            }
        }
    };

    let code1 = quote! {
        #type_def
        #state_def
        #block_def
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
                    _ => &format!("{:?}", self),
                };
                write!(f, "{}", s0)
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

        fn main() {
            let tm = TuringMachine::from_standard_notation(TM_DEF);
        }
    };

    let syntax_tree1 = syn::parse2(code1).unwrap();
    let formatted1 = prettyplease::unparse(&syntax_tree1);
    let mut file1 = fs::OpenOptions::new()
                .read(true)
                .write(true)
                .truncate(true)
                .open("higher_rule_generated_code_part1.txt").unwrap();
    file1.write_all(format!("// Start of autogenerated code\n{formatted1}\n// End of autogenerated code").as_bytes()).unwrap();

    let syntax_tree2 = syn::parse2(code2).unwrap();
    let formatted2 = prettyplease::unparse(&syntax_tree2);
    let mut file2 = fs::OpenOptions::new()
                .read(true)
                .write(true)
                .truncate(true)
                .open("higher_rule_generated_code_part2.txt").unwrap();
    file2.write_all(format!("// Start of customizable code\n{formatted2}\n// End of customizable code").as_bytes()).unwrap();
}