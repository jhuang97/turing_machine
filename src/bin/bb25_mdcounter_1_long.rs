use std::{
    collections::{HashMap, VecDeque},
    fmt,
    path::Path,
};

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum HeadType {
    A,
    B,
    AR,
}

#[derive(Clone, Copy)]
struct Exp {
    a: u64,
    b: u128,
}

#[derive(Clone, Copy)]
struct Head {
    ty: HeadType,
    exp: Exp,
    index: usize,
}

impl fmt::Display for Head {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.ty {
            HeadType::A | HeadType::AR => write!(f, "A")?,
            HeadType::B => write!(f, "B")?,
        }
        write!(f, "({},{})", self.exp.a, self.exp.b)?;
        if self.ty == HeadType::AR {
            write!(f, " R")?;
        }
        Ok(())
    }
}

#[derive(PartialEq, Eq, Copy, Clone)]
enum Symbol {
    V,
    C,
    C1,
    R,
    R2,
}

impl fmt::Display for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use Symbol::*;
        let out = match self {
            V => "V",
            C => "0",
            C1 => "1",
            R => " R",
            R2 => " R2",
        };
        write!(f, "{}", out)
    }
}

struct Sim {
    left_a: u64,
    tape: VecDeque<Symbol>,
    head: Option<Head>,
    self_steps: u64,
}

impl fmt::Display for Sim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}: B({},1)^inf ", self.self_steps, self.left_a)?;

        if let Some(head) = self.head {
            if head.ty == HeadType::AR {
                for s in &self.tape {
                    write!(f, "{}", s)?;
                }
                write!(f, " {}", head)?;
            } else {
                for i in 0..head.index {
                    write!(f, "{}", self.tape[i])?;
                }
                if head.index > 0 {
                    write!(f, " ")?;
                }
                write!(f, "{} ", head)?;
                for i in head.index..self.tape.len() {
                    write!(f, "{}", self.tape[i])?;
                }
            }
        } else {
            for s in &self.tape {
                write!(f, "{}", s)?;
            }
        }

        Ok(())
    }
}

impl Sim {
    fn new() -> Self {
        use Symbol::*;
        Self {
            left_a: 6,
            tape: VecDeque::from([C1, C, C1, C1, R2]),
            head: None,
            self_steps: 0,
        }
    }

    fn step(&mut self) {
        use HeadType::*;
        use Symbol::*;
        if let Some(h) = &mut self.head {
            let b = h.exp.b;
            match (h.ty, b % 2 == 0, &self.tape[h.index]) {
                (B, _, V) => {
                    h.exp.a += 1;
                    h.exp.b = b * 2 - 1;
                    h.index += 1;
                }
                (B, true, C) => {
                    h.exp.a -= 1;
                    h.exp.b = b / 2 + 3;
                    h.index += 1;
                }
                (B, false, C) => {
                    h.exp.a -= 1;
                    h.exp.b = b / 2 + 4;
                    self.tape[h.index] = C1;
                    h.index += 1;
                }
                (B, _, C1) => {
                    if self.tape.get(h.index + 1) == Some(&R2) {
                        h.ty = A;
                        h.exp.b += 7;
                        self.tape.truncate(h.index);
                        self.tape.push_back(C);
                        self.tape.push_back(C);
                        self.tape.push_back(C);
                        self.tape.push_back(R);
                    } else {
                        h.exp.a += 1;
                        h.exp.b = b * 2 + 1;
                        self.tape[h.index] = V;
                        h.index += 1;
                    }
                }
                (A, true, C | C1) => {
                    h.exp.a -= 1;
                    h.exp.b /= 2;
                    h.index += 1;
                    if self.tape.get(h.index) == Some(&R) {
                        assert!(self.tape.len() == h.index + 1);
                        self.tape.pop_back();
                        h.index -= 1;
                        h.ty = AR;
                    }
                }
                (A, false, C) => {
                    h.exp.a -= 1;
                    h.exp.b = b / 2 + 1;
                    self.tape[h.index] = C1;
                    h.index += 1;
                    if self.tape.get(h.index) == Some(&R) {
                        assert!(self.tape.len() == h.index + 1);
                        self.tape.pop_back();
                        h.index -= 1;
                        h.ty = AR;
                    }
                }
                (AR, true, _) => {
                    self.tape.push_back(C);
                    h.exp.a -= 1;
                    h.exp.b = b / 2 + 1;
                }
                (AR, false, _) => {
                    if h.exp.b == 3 {
                        for _ in 0..(h.exp.a - 2) {
                            self.tape.push_back(C1);
                        }
                        self.tape.push_back(R2);
                        self.head = None;
                    } else {
                        self.tape.push_back(C1);
                        h.exp.a -= 1;
                        h.exp.b = b / 2 + 2;
                    }
                }
                _ => unimplemented!(),
            }
        } else {
            if self.tape.front() == Some(&V) {
                while self.tape.front() == Some(&V) {
                    self.tape.pop_front();
                    self.left_a += 1;
                }
            } else {
                self.head = Some(Head {
                    ty: HeadType::B,
                    exp: Exp {
                        a: self.left_a,
                        b: 1,
                    },
                    index: 0,
                });
            }
        }
        self.self_steps += 1;
    }

    fn to_string_alt(&self) -> String {
        let mut out = String::new();
        out.push_str(&format!("{:4}: {:4}", self.self_steps, self.left_a));
        if let Some(head) = self.head {
            out.push_str(&format!(" ... {:4} {:128b}", head.exp.a, head.exp.b));

            match head.ty {
                HeadType::AR => {
                    out.push_str(" AR");
                }
                HeadType::B => {
                    out.push_str(" B");
                    if let Some(s) = self.tape.get(head.index) {
                        out.push_str(&format!(" {s}"));
                        if self.tape.get(head.index + 1) == Some(&Symbol::R2) {
                            out.push_str("R2");
                        }
                    }
                }
                HeadType::A => {
                    out.push_str(" A ");
                    for i in head.index..self.tape.len() {
                        out.push_str(&format!("{}", self.tape[i]));
                    }
                }
            }
        }
        out
    }
}

struct LongDiagram {
    row: usize,
    map: HashMap<(usize, usize), Symbol>,
}

impl LongDiagram {
    fn new() -> Self {
        Self {
            row: 0,
            map: HashMap::new(),
        }
    }

    fn record_tape(&mut self, horizontal_offset: usize, tape: &VecDeque<Symbol>) {
        let mut x = horizontal_offset;
        for s in tape {
            self.map.insert((self.row, x), *s);
            x += 1;
        }
        self.row += 1;
    }

    fn save_image<P>(&self, path: P)
    where
        P: AsRef<Path>,
    {
        let mut width = 0u32;
        let mut height = 0u32;
        for (r, c) in self.map.keys() {
            width = width.max((c + 1) as u32);
            height = height.max((r + 1) as u32);
        }

        #[derive(Default, Clone)]
        struct Pixel {
            r: u8,
            g: u8,
            b: u8,
        }

        let mut data: Vec<Vec<Pixel>> =
            vec![vec![Pixel::default(); width as usize]; height as usize];

        for (&(r, c), s) in &self.map {
            use Symbol::*;
            let pixel = match s {
                V => Pixel { r: 255, g: 0, b: 0 },
                C => Pixel { r: 0, g: 0, b: 255 },
                C1 => Pixel { r: 0, g: 255, b: 0 },
                R => Pixel {
                    r: 20,
                    g: 20,
                    b: 20,
                },
                R2 => Pixel {
                    r: 128,
                    g: 128,
                    b: 128,
                },
            };
            data[r][c] = pixel;
        }

        let data_flat: Vec<u8> = data
            .into_iter()
            .flatten()
            .map(|p| [p.r, p.g, p.b, 255])
            .flatten()
            .collect();

        use std::fs::File;
        use std::io::BufWriter;
        let file = File::create(path).unwrap();
        let w = &mut BufWriter::new(file);
        let mut encoder = png::Encoder::new(w, width, height);
        encoder.set_color(png::ColorType::Rgba);
        encoder.set_depth(png::BitDepth::Eight);
        let mut writer = encoder.write_header().unwrap();
        writer.write_image_data(&data_flat).unwrap();
    }
}

fn main() {
    let mut sim = Sim::new();
    println!("{sim}");
    let mut diagram = LongDiagram::new();
    diagram.record_tape(sim.left_a as usize, &sim.tape);

    let max_steps = 863;
    for k in 0..=max_steps {
        sim.step();
        diagram.record_tape(sim.left_a as usize, &sim.tape);
        println!("{sim}");
        // println!("{}", sim.to_string_alt());
    }

    // diagram.save_image("bb25_mdcounter_1_long_diagram.png");
}
