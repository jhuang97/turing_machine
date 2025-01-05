mod skelet1;

use std::{collections::HashMap, error::Error, hash::Hash, ops::{Add, AddAssign}, str::FromStr};

use itertools::izip;
use skelet1::{counter_to_rle, counter_transition_rules, left_block_definition, Binomial, CounterBlockType, CounterSimulator, CounterStepInfo, CounterSymbol, Direction, NSteps};
use turing_machine::{BasicSimulator, State, Symbol, TMDirection, TMTransition, TuringMachine};

const SKELET_1: &str = "1RB1RD_1LC0RC_1RA1LD_0RE0LB_---1RC";
const TM_13502512: &str = "1RB1LD_1LC1RE_---1LD_1LA0LD_0RE0RC";
const HALT_105: &str = "1RB1LC_0LB1LA_1RD1LB_1RE0RD_0RA---";

fn is_skelet1_basic_state(sim: &BasicSimulator) -> bool {
    (sim.state == State::A && sim.prev_dir == Some(TMDirection::Right) && (*sim.tape.get(sim.position).unwrap() == Symbol(1) || sim.position == sim.tape.len()-1)) ||
    (sim.state == State::C && sim.prev_dir == Some(TMDirection::Left))
}

fn compare_basic_rle_skelet(n_steps: usize) {
    let tm = TuringMachine::from_standard_notation(SKELET_1);
    let mut basic = BasicSimulator::new(tm);
    let mut rle = skelet1::RLESimulator::new();

    for _ in 0..n_steps {
        while basic.time < rle.base_steps {
            basic.step();
        }
        println!("{rle}");
        println!("{}", basic.display_directed_head());
        rle.step().unwrap();
    }
}

fn compare_rle_counter_skelet(n_steps: usize) {
    let mut rle = skelet1::RLESimulator::new();
    let mut counter = skelet1::CounterSimulator::new(false);

    for _ in 0..n_steps {
        while rle.rle_steps < counter.rle_steps as usize {
            rle.step().unwrap();
        }
        println!("{counter}");
        println!("{rle}");
        counter.step().unwrap();
    }
}

fn compare_counter_stride_skelet(n_steps: usize) {
    let mut sim = skelet1::CounterSimulator::new(false);
    let mut sim_stride = skelet1::CounterSimulator::new(true);

    for _ in 0..=n_steps {
        while sim.rle_steps < sim_stride.rle_steps {
            sim.step().unwrap();
        }
        println!("{sim_stride:>width$}", width=(sim.self_steps.checked_ilog10().unwrap_or(0) + 1) as usize);
        println!("{sim}");
        sim_stride.step().unwrap();
    }
}

fn check_rle_to_counter() {
    for (&k, v) in counter_to_rle() {
        print!("{:?}: ", k);
        for s in v {
            print!("{}", s.0);
        }
        println!();
    }
}

fn check_counter_transition_rules() {
    println!("rule #: rule (rle steps, base steps)");
    for (i, rule) in counter_transition_rules().iter().enumerate() {
        print!("{}: {rule} ", i);
        if !rule.has_xn {
            let (rle_steps, base_steps) = skelet1::validate_counter_rule(rule, None).unwrap();
            println!("({}, {})", rle_steps, base_steps);
        } else {
            let (rle_steps, base_steps) = skelet1::validate_counter_rule(rule, Some(1)).unwrap();
            for exp in 2..8 {
                let (r_mult, b_mult) = skelet1::validate_counter_rule(rule, Some(exp)).unwrap();
                assert_eq!(rle_steps * exp, r_mult);
                assert_eq!(base_steps * exp, b_mult);
            }
            println!("({} * n, {} * n)", rle_steps, base_steps);
        }
    }
}

fn measure_partial_stride(counts: &mut HashMap<usize, u128>, n_counts: &mut HashMap<usize, Binomial>, 
    rtape: &Vec<CounterSymbol>, r_xnr_idx: usize, N0: u128, N1: u128) {
    use CounterSymbol::*;
    
    let mut rtape_rev: Vec<CounterSymbol> = rtape[r_xnr_idx+1..].iter().rev().cloned().collect(); // chop off the right block
    rtape_rev.push(R); // we will also count the number of times the head bounces off of this substitute R - this is a way to count # strides to the right
    let split: Vec<_> = rtape_rev.split(|&s| s == C).collect();

    // w_i = (x|D)*

    // > w0 R ==> < w0 R
    // stride level 0
    if split.len() == 1 {
        let mut n_x: Binomial = Binomial::default();
        let mut n_D = 0;
        for symb in split[0] {
            match symb {
                X(n) => n_x += n_infer(*n, N0, N1),
                D => n_D += 1,
                R => continue,
                _ => unreachable!()
            }
        }

        *n_counts.entry(0).or_default() += n_x; // N_X_LEFT
        *n_counts.entry(3).or_default() += n_x; // N_X_RIGHT

        *counts.entry(4).or_default() += n_D; // N_D_RIGHT
        *counts.entry(1).or_default() += n_D; // N_D_LEFT
        *counts.entry(5).or_default() += 1;   // right stride
    } else {
        let mut powers_4: Vec<u128> = vec![1];

        // Verify that there are enough x's to the left of each C
        for (i, &part) in (&split[..split.len()-1]).iter().enumerate() {
            let n_eat = if i == 0 {
                1
            } else {
                let n_new = powers_4[i-1] * 4;
                powers_4.push(n_new);
                n_new
            };

            match part.split_last() {
                Some((X(exp), _)) => if *exp < n_eat { unreachable!() },
                _ => unreachable!(),
            }
        }
        powers_4.push(powers_4.last().unwrap() * 4);

        // > w0 x C     w1 x^4 C     ... w_n x^4^n C           w_{n+1} R ==>
        // < w0   C x^2 w1     C x^8 ... w_n       C x^(2*4^n) w_{n+1} R

        // stride level is n+1, since there are n+1 C's

        // count the number of x's and D's in each w_i; the x's to be eaten by a C do not count
        let n = split.len() - 2;
        let mut n_x: Vec<Binomial> = Vec::new();
        let mut n_D: Vec<u32> = Vec::new();
        for (i, &part) in split.iter().enumerate() {
            let mut curr_n_x = Binomial::default();
            let mut curr_n_D = 0;
            for symb in part {
                match symb {
                    X(exp) => curr_n_x += n_infer(*exp, N0, N1),
                    D => curr_n_D += 1,
                    R => (),
                    _ => unreachable!()
                }
            }
            if i <= n {
                curr_n_x.checked_sub_const_assign(powers_4[i]);
            }
            n_x.push(curr_n_x);
            n_D.push(curr_n_D);
        }

        // rules count

        // count the w's
        assert!(powers_4.len() >= n_x.len());
        for (pow, curr_n_x, curr_n_D) in izip!(&powers_4, n_x, n_D) {
            *n_counts.entry(0).or_default() += curr_n_x * pow; // N_X_LEFT
            *n_counts.entry(3).or_default() += curr_n_x * pow; // N_X_RIGHT

            *counts.entry(4).or_default() += curr_n_D as u128 * pow; // N_D_RIGHT
            *counts.entry(1).or_default() += curr_n_D as u128 * pow; // N_D_LEFT
        }

        // count number of times the head goes off to the right
        *counts.entry(5).or_default() += powers_4[n+1];   // right stride
        
        // count the C's
        let a1 = powers_4[n+1] - 1;
        let a2 = a1 / 3;
        let p16 = 1u128.checked_shl(4 * (n as u32 + 1)).unwrap();
        let rep_x_both = ((p16 - 1) / 15 - a2) * 9 / 2;
        let rep_x_left = a2 * 4;
        (*n_counts.entry(0).or_default()).checked_add_const_assign(rep_x_both + rep_x_left); // N_X_LEFT
        (*n_counts.entry(3).or_default()).checked_add_const_assign(rep_x_both + a1); // N_X_RIGHT

        for type_id in [8, 9, 10, 2, 7] { // N_C0_LEFT, N_C1_LEFT, N_C2_LEFT, N_C_LEFT, N_C_RIGHT
            *counts.entry(type_id).or_default() += a2;
        }
    }
}

fn to_sorted_pairs<T>(map: &HashMap<usize, T>) -> Vec<(usize, T)> 
where T: Clone
{
    let mut v: Vec<(usize, T)> = map.iter().map(|(a, b)| (*a, b.clone())).collect();
    v.sort_by_key(|x| x.0);
    v
}

fn add_counts<'a, T>(a: &'a HashMap<usize, T>, b: &'a HashMap<usize, T>) -> HashMap<usize, T>
where T: 'a + AddAssign<&'a T> + Default
{
    let mut out = HashMap::new();

    for counts in [a, b] {
        for (id, count) in counts {
            *out.entry(*id).or_default() += count;
        }
    }

    out
}

/// Write the @uni-cycle rule as
///    J x^(n+P) C1 D >       r   -->
///  F J x^n     C1 D > G s^T(r)
/// The x^(n+P) block of the @uni-cycle rule gradually becomes x^n, while the head passes through it a bunch of times.
/// Try to count the steps due to x^n and the steps due to the other x's.
/// 
/// I also let N1 = n + P, N0 = n.
/// 
/// Need to count the number of times the counter rules are applied over the course of one uni-cycle.
/// Due to the x^n block, some rule counts need to be generic over the size of the x^n block.
/// Here, I use the Binomial struct to count those.
/// I think of a Binomial instance as a0 + a1 * N.  Here N refers to N0.
fn measure_uni_cycle(do_print: bool, N0: u128, nr1: u128) {
    use CounterSymbol::*;
    use CounterBlockType::*;
    use CounterStepInfo::*;

    const P: u128 = 53946;
    let N1: u128 = N0 + P;
    let mut ltape = vec![L];
    ltape.extend_from_slice(left_block_definition()[&J].as_slice());
    ltape.extend(vec![X(N1), C1, D]);

    let mut rtape = vec![X(nr1), D, X(1000000), C, X(1000000), R];
    let r_xnr_idx = rtape.len() - 1;
    rtape.reverse();

    let mut sim = CounterSimulator {
        left_tape: ltape,
        right_tape: rtape,
        dir: Direction::Right,
        base_steps: 0,
        rle_steps: 0,
        do_strides: true,
        self_steps: 0
    };

    let mut stride_times: Vec<_> = Vec::new();
    let mut stride_levels: Vec<usize> = Vec::new();
    let mut stride_rtapes: Vec<Vec<CounterSymbol>> = Vec::new();
    let mut n_strides_right: usize = 0;
    let mut rule_count: HashMap<usize, u128> = HashMap::new();
    let mut exp_rules: Vec<CounterStepInfo> = Vec::new();

    let mut exp_total: HashMap<usize, Binomial> = HashMap::new();

    let mut stride_counter_rule_counts: HashMap<usize, u128> = HashMap::new();
    let mut stride_counter_rule_n_counts: HashMap<usize, Binomial> = HashMap::new();

    let mut r_strides_step_count_prediction: Option<NSteps> = None;

    for i in 0..4000 {
        let mut sim_r = sim.clone();
        sim_r.rewrite_with_blocks(&vec![J], &vec![]);
        if do_print {
            println!("{}", sim_r);
        }

        if sim_r.left_tape.contains(&Block(J, 1)) &&
            sim_r.dir == Direction::Right &&
            sim_r.left_tape.ends_with(&[C1, D])
        {
            sim_r.rewrite_with_blocks(&vec![LeftDebris, A, G], &vec![G]);
            println!("{}", sim_r);

            for &level in &stride_levels {
                assert!(level >= 1);
                n_strides_right += 4usize.pow(level as u32 - 1);
            }

            if i == 0 {
                let mut sim2 = sim.clone();
                r_strides_step_count_prediction = Some(sim2.multi_stride(215779).unwrap().1);
            }

            if i > 0 {
                // println!("strides: {} {:?} ({}, {})", n_strides_right, stride_levels, stride_levels.len(), stride_rtapes.len());
                n_strides_right = 0;

                // println!("right tapes before applications of stride rule:");
                // for (idx, rtape) in stride_rtapes.iter().enumerate() {
                //     print!("{}/{}: ", idx+1, stride_rtapes.len());
                //     for symb in rtape {
                //         print!("{} ", symb);
                //     }
                //     println!();
                // }
                
                // print!("rule count: ");
                // for (id, count) in to_sorted_pairs(&rule_count) {
                //     print!("S{}: {}, ", id, count);
                // }
                // println!();

                // print!("N rule count: ");
                // for (id, count) in to_sorted_pairs(&exp_total) {
                //     print!("S{}: {}, ", id, count);
                // }
                // println!();

                // print!("stride rule count: ");
                // for (id, count) in to_sorted_pairs(&stride_counter_rule_counts) {
                //     if id == 5 {
                //         print!("(right stride): {}, ", count);
                //     } else {
                //         print!("S{}: {}, ", id, count);
                //     }
                // }
                // println!();

                // print!("stride rule N count: ");
                // for (id, count) in to_sorted_pairs(&stride_counter_rule_n_counts) {
                //     print!("S{}: {}, ", id, count);
                // }
                // println!();

                println!("predicted steps:");
                println!("{:?}", skelet1::N_SINGLE_UNICYCLE_CONST + skelet1::N_SINGLE_UNICYCLE_N * N0 + r_strides_step_count_prediction.clone().unwrap());

                let total_counts_normal = add_counts(&rule_count, &stride_counter_rule_counts);
                let total_counts_N = add_counts(&exp_total, &stride_counter_rule_n_counts);
                print!("totals (normal): ");
                for (id, count) in to_sorted_pairs(&total_counts_normal) {
                    if id == 5 {
                        print!("(right stride): {}, ", count);
                    } else {
                        print!("S{}: {}, ", id, count);
                    }
                }
                println!();

                print!("totals (N): ");
                for (id, count) in to_sorted_pairs(&total_counts_N) {
                    print!("S{}: {}, ", id, count);
                }
                println!();

                // println!("{:?}", exp_rules);
            }

            if sim.self_steps > 0 {
                return;
            }

            stride_rtapes.clear();
            stride_levels.clear();
            rule_count.clear();
            exp_rules.clear();
            exp_total.clear();

            // I don't have a good way to reset the stride counter rule counting yet
            // would need to update N0, N1, and r_xnr_idx in addition to clearing these two hashmaps
            stride_counter_rule_counts.clear();
            stride_counter_rule_n_counts.clear();
        }

        if sim.can_do_stride() {
            stride_rtapes.push(sim.right_tape.clone());
            measure_partial_stride(&mut stride_counter_rule_counts, &mut stride_counter_rule_n_counts,
                &sim.right_tape, r_xnr_idx, N0, N1);
        }

        match sim.step().unwrap() {
            Stride { level} => {
                stride_times.push(sim.self_steps);
                stride_levels.push(level);
            },
            S(id) => {
                *rule_count.entry(id).or_default() += 1;
            },
            r @ _ => {
                exp_rules.push(r);
                let (type_id, exp) = match r {
                    S0(n) => (0, n),
                    S3(n) => (3, n),
                    S23(n) => (23, n),
                    _ => unreachable!()
                };

                *exp_total.entry(type_id).or_default() += n_infer(exp, N0, N1);
            },
        }
        assert_eq!(sim.right_tape.get(r_xnr_idx), Some(&X(nr1)));
    }
}

fn n_infer(exp: u128, N0: u128, N1: u128) -> Binomial {
    if exp < N0 {
        Binomial { a0: exp, a1: 0 }
    } else if N0 <= exp && exp <= N1 {
        Binomial { a0: exp-N0, a1: 1 }
    } else {
        unreachable!()
    }
}

fn main() {
    // dbg!(TuringMachine::from_standard_notation(SKELET_1));
    let tm = TuringMachine::from_standard_notation(SKELET_1);

    // let mut sim = BasicSimulator::new(tm);

    // for _ in 0..100 {
    //     println!("{sim}");
    //     sim.step();
    // }

    // println!("{}", sim.display_directed_head());
    // for _ in 0..400 {
    //     sim.step();
    // // while !sim.step() {
    //     print!("{}", sim.display_directed_head());
    //     if is_skelet1_basic_state(&sim) {
    //         println!(" =======");
    //     } else {
    //         println!();
    //     }
    // }

    // compare_basic_rle_skelet(50);
    // compare_rle_counter_skelet(200);
    // compare_counter_stride_skelet(8600);

    // let mut sim = skelet1::RLESimulator::new();

    // let mut sim = skelet1::CounterSimulator::new(false);
    // for i in 0..1000i64 {
    //     sim.step().unwrap();
    //     // if (i+1) % 100000000 == 0 {
    //         println!("{}", sim);
    //     // }
    // }

    // prototype stride
    // let mut sim = skelet1::CounterSimulator::new(false);
    // for i in 0..840 {
    //     sim.step().unwrap();
    //     println!("{}", sim);
    //     if [99, 157, 565, 661, 685, 699, 750, 840].contains(&(i+1)) {
    //         let rtape_rev: Vec<CounterSymbol> = sim.right_tape.iter().rev().cloned().collect();
    //         let split: Vec<_> = rtape_rev.split(|&s| s == CounterSymbol::C).collect();
    //         println!("split into {} parts", split.len());
    //         for ss in split {
    //             print!("split: ");
    //             for s in ss {
    //                 print!("{} ", s);
    //             }
    //             println!();
    //         }
    //     }
    // }

    // try sim with strides
    // let mut sim = skelet1::CounterSimulator::new(true);
    // for i in 0..68000 {
    //     sim.step().unwrap();
    // }
    // for i in 0..20000 { // 1300000
    //     sim.step().unwrap();
    //     {
    //         use CounterBlockType::*;
    //         use CounterSymbol::*;

    //         let mut sim_r = sim.clone();
    //         sim_r.rewrite_with_blocks(&vec![J], &vec![]);
    //         if sim_r.left_tape.contains(&Block(J, 1)) &&
    //             sim_r.dir == Direction::Right &&
    //             sim_r.left_tape.ends_with(&[C1, D])
    //         {
    //             sim_r.rewrite_with_blocks(&vec![LeftDebris, A, G], &vec![G]);
    //             println!("{}", sim_r);
    //         }
    //     }
    // }

    measure_uni_cycle(false, 100000000, 100);
    measure_uni_cycle(false, 100000000, 1000);
    measure_uni_cycle(false, 1000000000, 100);

    // skelet1::count_G_block_steps();
    // skelet1::add_up_steps_for_one_uni_cycle();

    // check_rle_to_counter();

    // println!("{}", sim.display_directed_head());

    // check_counter_transition_rules();

    // for (i, rule) in counter_transition_rules().iter().enumerate() {
    //     print!("S{}.  {rule} ", i);
    //     if !rule.has_xn {
    //         let (rle_steps, base_steps) = skelet1::validate_counter_rule(rule, None).unwrap();
    //         println!("({})", base_steps);
    //     } else {
    //         let (rle_steps, base_steps) = skelet1::validate_counter_rule(rule, Some(1)).unwrap();
    //         for exp in 2..8 {
    //             let (r_mult, b_mult) = skelet1::validate_counter_rule(rule, Some(exp)).unwrap();
    //             assert_eq!(rle_steps * exp, r_mult);
    //             assert_eq!(base_steps * exp, b_mult);
    //         }
    //         println!("({} * n)", base_steps);
    //     }
    // }

    // println!("{sim}");
    // while !sim.step() {
    //     println!("{sim}");
    // }
    // println!("{sim}");
}
