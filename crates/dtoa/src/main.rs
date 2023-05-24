use std::f64::consts::PI;
use std::fmt::Display;

struct Float64 {
    sign: bool,
    biased_exp: i16,
    frac: u64,
}

impl Float64 {
    fn significand(&self) -> u64 {
        0x10000000000000 + self.frac
    }

    fn exp(&self) -> i16 {
        self.biased_exp - 1023
    }

    fn to_dec(self) -> String {
        let mut buffer = String::new();

        if self.sign {
            buffer.push('-')
        }

        let exp = 52 - self.exp();

        let mut n = self.significand();

        buffer += &(n >> exp).to_string();

        buffer.push('.');

        let mark = (1 << exp) - 1;

        n &= mark;
        for _ in 0..16 {
            n *= 10;
            buffer += &(n >> exp).to_string();
            n &= mark
        }

        buffer
    }
}

impl From<f64> for Float64 {
    fn from(f: f64) -> Self {
        let bits = f.to_bits();
        Float64 {
            sign: (bits >> 63) != 0,
            biased_exp: ((bits >> 52) as i16) & 0x7ff,
            frac: bits & 0xfffffffffffff,
        }
    }
}

impl Display for Float64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {:0>11b} {:0>52b}",
            if self.sign { '1' } else { '0' },
            self.biased_exp,
            self.frac
        )
    }
}

fn main() {
    println!("{}", Float64::from(6.02214076e10).to_dec());
    println!("{}", Float64::from(PI).to_dec());
}
