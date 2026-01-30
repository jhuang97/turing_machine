use std::{fmt, sync::OnceLock};

use num_traits::{One, Zero};
use num_integer::Integer;

type ListNum = num_bigint::BigUint;

fn two() -> &'static ListNum {
    static TWO: OnceLock<ListNum> = OnceLock::new();
    TWO.get_or_init(|| ListNum::from(2u8))
}
fn three() -> &'static ListNum {
    static THREE: OnceLock<ListNum> = OnceLock::new();
    THREE.get_or_init(|| ListNum::from(3u8))
}
fn four() -> &'static ListNum {
    static FOUR: OnceLock<ListNum> = OnceLock::new();
    FOUR.get_or_init(|| ListNum::from(4u8))
}
fn five() -> &'static ListNum {
    static FIVE: OnceLock<ListNum> = OnceLock::new();
    FIVE.get_or_init(|| ListNum::from(5u8))
}
fn six() -> &'static ListNum {
    static SIX: OnceLock<ListNum> = OnceLock::new();
    SIX.get_or_init(|| ListNum::from(6u8))
}

fn print_max() -> &'static ListNum {
    static MAX: OnceLock<ListNum> = OnceLock::new();
    MAX.get_or_init(|| ListNum::from(u128::MAX))
}

struct ListSim {
    left: Vec<ListNum>,
    mid: ListNum,
    right: Vec<ListNum>,
    halted: bool,
    self_steps: u64
}

fn fmt_list_num(n: &ListNum, f: &mut fmt::Formatter) -> fmt::Result {
    if n <= print_max() {
        write!(f, "{}", n)
    } else {
        if n.is_even() {
            write!(f, "({} bits, even)", n.bits())
        } else {
            write!(f, "({} bits, odd)", n.bits())
        }
    }
}

impl fmt::Display for ListSim {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, " {}: ", self.self_steps)?;

        for n in &self.left {
            fmt_list_num(n, f)?;
            write!(f, " ")?;
        }
        write!(f, "[")?;
        fmt_list_num(&self.mid, f)?;
        write!(f, "]")?;
        for n in self.right.iter().rev() {
            write!(f, " ")?;
            fmt_list_num(n, f)?;
        }
        if self.halted {
            write!(f, " HALTED")?;
        }

        Ok(())
    }
}

fn add_or_merge(v: &mut Vec<ListNum>, nadd: &ListNum) {
    if let Some(last) = v.last_mut() {
        *last += nadd;
    } else {
        v.push(nadd.clone());
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum ListRule {
    R1a, R1b, R2, R7, R8, R10, R5, R11, R4, R12,
    R3, R13, R14, R15
}

impl ListSim {
    fn new() -> Self {
        Self {
            left: vec![],

            // The original TM reaches a ListSim configuration of [2] at 8 steps,
            // [5] at 32 steps, [8] at 71 steps
            mid: two().clone(),
            right: vec![],
            halted: false,
            self_steps: 0,
        }
    }

    fn step(&mut self) -> (bool, ListRule) {
        use ListRule::*;

        let rule = match (self.mid.clone(), self.left.as_slice(), self.right.as_slice()) {
            // 1a. ... a [4k]> b ... -> ... a+k [0]> b+3k ... (k >= 1)
            (n, _, _) if n.is_multiple_of(four()) && n >= *four() => {
                let k = n/4u8;
                add_or_merge(&mut self.left, &k);
                self.mid = ListNum::ZERO;
                add_or_merge(&mut self.right, &(k*3u8));
                R1a
            }

            // 1b. ... a [4k+2]> b ... -> ... a+k+2 [b+3k+1]> ...
            (n, _, _) if &n % 4u8 == *two() && n >= *two() => {
                let k = n/4u8;
                add_or_merge(&mut self.left, &(&k+2u8));
                self.mid = k*3u8 + 1u8 + self.right.pop().unwrap_or_default();
                R1b
            }

            // 2. L 2 [2k+3]> b ... -> L [b+6k+11]> ...
            (n, [nl], _) if n.is_odd() && n >= *three() && *nl == *two() => {
                self.left.clear();
                self.mid = n * 3u8 + 2u8 + self.right.pop().unwrap_or_default();
                R2
            }

            // 7. L 2 [0]> c ... -> L 2 [c+2]> ...
            (n, [nl], _) if n.is_zero() && *nl == *two() => {
                self.mid = 2u8 + self.right.pop().unwrap_or_default();
                R7
            }

            // 8. L 4 [0]> c ... -> L [c+8]> ...
            (n, [nl], _) if n.is_zero() && *nl == *four() => {
                self.left.clear();
                self.mid = 8u8 + self.right.pop().unwrap_or_default();
                R8
            }

            // reduced 10. L 2k_0+3 [2k_n+3]> c ... -> L 2 [2k_0+1]> 2k_n+1 c+3 ...
            (n, [nl0], _) if n >= *three() && *nl0 >= *three()
                                                && nl0.is_odd() && n.is_odd() => {
                self.mid = nl0 - 2u8;
                self.left.clear();
                self.left.push(two().clone());
                
                add_or_merge(&mut self.right, three());
                self.right.push(n - 2u8);
                R10
            }

            // reduced 12. L 2k_0+4 [2k_n+3]> c ... -> L 1 [2k_0+2]> 2k_n+1 c+3 ...
            (n, [nl0], _) if n >= *three() && *nl0 >= *four() 
                                                && nl0.is_even() && n.is_odd() => {
                self.mid = nl0 - 2u8;
                self.left.clear();
                self.left.push(ListNum::one());
                
                add_or_merge(&mut self.right, three());
                self.right.push(n - 2u8);
                R12
            }

            // 5. L 2k+5 [0]> c ... --> L 2 [2k+1]> c+4 (c >= 0)
            (n, [nl0], _) if n.is_zero() && *nl0 >= *five() && nl0.is_odd() => {
                self.mid = nl0 - 4u8;
                self.left.clear();
                self.left.push(two().clone());
                
                add_or_merge(&mut self.right, four());
                R5
            }

            // 11. L [2k+5]> c ... -> L 2 [2k+1]> c+3 ...
            (n, [], _) if n.is_odd() && n >= *five() => {
                self.left.push(two().clone());
                self.mid -= 4u8;
                add_or_merge(&mut self.right, three());
                R11
            }

            // 4. ... a 2k+6 [0]> c ... -> ... a+1 [2k+2]> c+4 ... (a,c >= 0)
            (n, [.., nl0], _)if *nl0 >= *six() && n.is_zero() && nl0.is_even() => {
                let nl = self.left.pop().unwrap();
                add_or_merge(&mut self.left, &ListNum::one());
                self.mid = nl - 4u8;
                add_or_merge(&mut self.right, four());
                R4
            }

            // the following have not been encountered in the original TM's forward simulation
            // 3. ... a [1]> c ... -> ... [a+c+3]> ... (a,c >= 0)
            (n, _, _) if n.is_one() => {
                self.mid = 3u8 + self.left.pop().unwrap_or_default() + self.right.pop().unwrap_or_default();
                R3
            }

            // 13. L 3 [0]> c ... -> ***HALT***
            (n, [nl], _) if n.is_zero() && *nl == *three() => {
                self.halted = true;
                self.self_steps += 1;
                return (true, R13);
            }

            // 14. L [3]> c ... -> ***HALT***
            (n, [], _) if n == *three() => {
                self.halted = true;
                self.self_steps += 1;
                return (true, R14);
            }

            // 15. L 1 [0]> c ... -> L [c+4]> ...
            (n, [nl], _) if n.is_zero() && nl.is_one() => {
                self.left.clear();
                self.mid = 4u8 + self.right.pop().unwrap_or_default();
                R15
            }
            
            _ => unimplemented!()
        };

        self.self_steps += 1;
        (false, rule)
    }
}

fn main() {
    let mut sim = ListSim::new();
    // let max_steps = 924;
    let max_steps = 10000000;
    println!("{sim}");

    for i in 1..=max_steps {
        let (halted, rule) = sim.step();
        if i % 100000 == 0 {
            println!("{rule:?} {sim}");
        }

        if halted {
            println!("halted!");
            break;
        }
        if sim.mid.bits() >= 8 * 100 * 1024 * 1024 {
            println!("more than 100 MB");
            break;
        }
    }
    println!("{sim}");
}