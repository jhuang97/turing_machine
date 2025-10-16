use turing_machine::wily_coyote::BlockSimulator;

fn main() {
    let mut sim = BlockSimulator::new();
    // let mut sim = {
    //     use BlockSymbol::*;
    //     use RunSymbolType::*;
    //     BlockSimulator::new_with_tape(vec![L, Run(X, 100), 
    //         Run(Q, 7), Run(X, 1), 
    //         Run(Q, 5), Run(X, 2),
    //         Run(Q, 1), Run(X, 1),
    //         Run(Q, 1), Run(X, 1),], 
    //         HigherState::Left,
    //         vec![R])
    // };

    // let max_steps = 30000;
    // let max_steps = 2000000000;
    let max_steps = 1000000000u64;
    // let max_steps = 10000000000u64;
    println!("{}", sim);
    for i in 1..=max_steps {
        let res = sim.step();
    //     // if i % 1 == 0 {
        // if sim.left_tape.len() >= 28 {
        if sim.right_tape.len() <= 6 {
        // if sim.state == HigherState::Left {
            println!("{}", sim);
        }
    //     // if let Some((a, c)) = sim.parse_special_state() {
    //         // if a == 1 {
    //             // println!("{a:8}, {c:8} | {sim}");
    //         // }
    //     // }
        if res.is_err() {
            println!("{}, {:?}", sim, res);
            // if let Some(n_symb) = sim.parse_halt_state() {
            //     println!("Halt({})", n_symb);
            // } else {
            //     println!("{:?}", res);
            // }
            break;
        }
    }
    println!("{}", sim);
}