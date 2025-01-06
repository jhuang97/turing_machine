mod skelet1;

use skelet1::{counter_to_rle, counter_transition_rules, measure_uni_cycle, CounterBlockType, CounterStepInfo, CounterSymbol, Direction};
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
    let mut counter = skelet1::CounterSimulator::new(false, false);

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
    let mut sim = skelet1::CounterSimulator::new(false, false);
    let mut sim_stride = skelet1::CounterSimulator::new(true, false);

    for _ in 0..=n_steps {
        while sim.rle_steps < sim_stride.rle_steps {
            sim.step().unwrap();
        }
        println!("{sim_stride:>width$}", width=(sim.self_steps.checked_ilog10().unwrap_or(0) + 1) as usize);
        println!("{sim}");
        sim_stride.step().unwrap();
    }
}

fn compare_counter_unicycle_skelet_set_position(n_steps: usize, n_cycle_left: u128, extra_left: u128, n_cycle_right: u128, extra_right: u128) {
    use CounterBlockType::*;
    use CounterSymbol::*;

    const UNI_CYCLE_P: u128 = 53946;
    const UNI_CYCLE_T: u128 = 215779;

    let lpart = [X(UNI_CYCLE_P*n_cycle_left+extra_left), C1, D];
    let ltape = [&[L, Block(J, 1)], &lpart[..]].concat();
    let ltape2 = [&[L], skelet1::left_block_definition()[&J].as_slice(), &lpart[..]].concat();

    let mut rtape = vec![X(100), D, X(UNI_CYCLE_T * n_cycle_right + extra_right), C, X(1000000), R];
    rtape.reverse();

    let mut sim_uni = skelet1::CounterSimulator {
        left_tape: ltape.clone(),
        right_tape: rtape.clone(),
        dir: Direction::Right,
        base_steps: 0,
        rle_steps: 0,
        self_steps: 0,
        do_strides: true,
        do_uni_cycles: true
    };

    let mut sim = skelet1::CounterSimulator {
        left_tape: ltape2,
        right_tape: rtape,
        dir: Direction::Right,
        base_steps: 0,
        rle_steps: 0,
        self_steps: 0,
        do_strides: true,
        do_uni_cycles: false
    };

    for i in 0..n_steps { // 1300000
        while sim.rle_steps < sim_uni.rle_steps {
            sim.step().unwrap();
        }

        let mut sim_uni_p = sim_uni.clone();
        sim_uni_p.rewrite_with_blocks(&vec![], &vec![]);

        assert!(!sim.right_tape.iter().any(|&e| if let Block(G, _) = e { true } else { false }));
        let mut sim_p = sim.clone();
        sim_p.rewrite_with_blocks(&vec![A, G, J], &vec![G]);

        println!("{sim_uni_p:>width$}", width=(sim.self_steps.checked_ilog10().unwrap_or(0) + 1) as usize);
        println!("{sim_p}");

        while sim_uni.rle_steps <= sim.rle_steps {
            sim_uni.step().unwrap();
        }
    }
}

fn compare_counter_unicycle_skelet(n_steps: usize) {
    use CounterBlockType::*;
    use CounterSymbol::*;

    let mut sim = skelet1::CounterSimulator::new(true, false);
    let mut sim_uni = skelet1::CounterSimulator::new(true, true);

    for i in 0..n_steps {
        while sim.rle_steps < sim_uni.rle_steps {
            sim.step().unwrap();
        }

        if i > 68000 {
            let mut sim_uni_p = sim_uni.clone();
            sim_uni_p.rewrite_with_blocks(&vec![LeftDebris], &vec![G]);

            assert!(!sim.right_tape.iter().any(|&e| if let Block(G, _) = e { true } else { false }));
            let mut sim_p = sim.clone();
            sim_p.rewrite_with_blocks(&vec![LeftDebris, A, G, J], &vec![G]);

            println!("{sim_uni_p:>width$}", width=(sim.self_steps.checked_ilog10().unwrap_or(0) + 1) as usize);
            println!("{sim_p}");
        }

        while sim_uni.rle_steps <= sim.rle_steps {
            sim_uni.step().unwrap();
        }
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

    // let mut sim = skelet1::CounterSimulator::new(false, false);
    // for i in 0..1000i64 {
    //     sim.step().unwrap();
    //     // if (i+1) % 100000000 == 0 {
    //         println!("{}", sim);
    //     // }
    // }

    // prototype stride
    // let mut sim = skelet1::CounterSimulator::new(false, false);
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
    // let mut sim = skelet1::CounterSimulator::new(true, false);
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

    // measure_uni_cycle(false, 100000000, 100);
    // measure_uni_cycle(false, 100000000, 1000);
    // measure_uni_cycle(false, 1000000000, 100);

    // skelet1::count_G_block_steps();
    // skelet1::add_up_steps_for_one_uni_cycle();

    // compare_counter_unicycle_skelet_set_position(5, 1, 0, 1, 0);
    // compare_counter_unicycle_skelet_set_position(5, 1, 1, 1, 1);
    // compare_counter_unicycle_skelet_set_position(5, 5, 0, 7, 1);
    // compare_counter_unicycle_skelet_set_position(5, 5, 1, 7, 0);
    // compare_counter_unicycle_skelet_set_position(5, 5, 1, 7, 1);
    // compare_counter_unicycle_skelet_set_position(5, 7, 10, 5, 10);

    // compare_counter_unicycle_skelet(68705);

    {
        use CounterBlockType::*;
        use CounterSymbol::*;
    
        let mut sim_uni = skelet1::CounterSimulator::new(true, true);

        fn n_J(v: &Vec<CounterSymbol>) -> usize {
            v.iter().filter(|x| x == &&Block(J, 1)).count()
        }
    
        for i in 0..1500001 {
            let res = sim_uni.step().unwrap();
            { // || (i > 69500 && i < 70000) || (i > 110610 && i < 110630) {
                let mut sim_uni_p = sim_uni.clone();
                sim_uni_p.rewrite_with_blocks(&vec![LeftDebris], &vec![]);
                let mut sim_uni_p2 = sim_uni.clone();
                sim_uni_p2.rewrite_with_blocks(&vec![LeftDebris, A, J, G], &vec![G]);
    
                if matches!(res, CounterStepInfo::UniCycle(_)) || (i > 68695 && i < 68705) || (i > 70000 && i % 50000 == 0) || 
                    (n_J(&sim_uni_p2.left_tape) > n_J(&sim_uni_p.left_tape) && sim_uni.dir == Direction::Right) {
                    println!("{sim_uni_p}");
                    println!("{sim_uni_p2}");
                }
            }
        }
    }

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
