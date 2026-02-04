use num_integer::Integer;

// 1RB0LD_0RC0RF_0RD0RA_1LE0RD_1LF---_0LA1LA
// 1RB0LD_0RC1RB_0RD0RA_1LE0RD_1LF---_0LA1LA

fn main() {
    let mut a: u128 = 4;
    let mut b: u128 = 11;

    let mut n_steps: u64 = 0;

    loop {
        if 2*a <= b {
            let mb = b - 2*a;
            (a, b) = (3*a+3, mb + 2);
        } else if 2*a == b + 1 {
            println!("HALT");
            break;
        } else if 2*a == b + 2 {
            println!("HALT");
            break;
        } else if b.is_even() {
            let mb = b/2;
            let ma = a - mb - 2;
            (a, b) = (ma, 3*mb + 5);
        } else {
            let mb = b/2;
            let ma = a - mb - 2;
            (a, b) = (ma, 3*mb + 8);
        }

        n_steps += 1;

        if n_steps % 500000000 == 0 {
            println!("{n_steps}: sum {}. B({a}, {b})", a+b);
        }
    }

    println!("{n_steps}: B({a}, {b})");
}