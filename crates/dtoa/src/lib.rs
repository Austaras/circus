use std::fmt::Display;

#[derive(Debug, Clone, Copy)]
pub struct Float64 {
    sign: bool,
    raw_exp: i16,
    frac: u64,
}

const EXP_LEN: i16 = 11;
const SGNFD_LEN: i16 = 52;

const EXP_BIAS: i16 = 2_i16.pow(EXP_LEN as u32 - 1) - 1;
const MAX_RAW_EXP: i16 = 2_i16.pow(EXP_LEN as u32) - 1;

impl Float64 {
    fn denormal(&self) -> bool {
        self.raw_exp == 0
    }

    fn exp(&self) -> i16 {
        if self.denormal() {
            1 - EXP_BIAS
        } else {
            self.raw_exp - EXP_BIAS
        }
    }

    pub fn to_dec(self) -> String {
        if self.raw_exp == MAX_RAW_EXP {
            let res = if self.frac == 0 {
                if self.sign {
                    "-Infinity".into()
                } else {
                    "Infinity".into()
                }
            } else {
                "NaN".into()
            };

            return res;
        }

        let mut buffer = String::new();

        if self.sign {
            buffer.push('-')
        }

        if self.denormal() {
        } else {
            let exp = SGNFD_LEN - self.exp();

            let mut n = self.frac + 0x10_0000_0000_0000;

            buffer += &(n >> exp).to_string();

            let mark = (1 << exp) - 1;

            n &= mark;

            if n != 0 {
                buffer.push('.');
                for _ in 0..16 {
                    n *= 10;
                    buffer += &(n >> exp).to_string();
                    n &= mark
                }
            }
        }

        buffer
    }
}

impl From<f64> for Float64 {
    fn from(f: f64) -> Self {
        let bits = f.to_bits();
        Float64 {
            sign: (bits >> 63) != 0,
            raw_exp: ((bits >> 52) as i16) & 0x7ff,
            frac: bits & 0xf_ffff_ffff_ffff,
        }
    }
}

impl Display for Float64 {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{} {:0>11b} {:0>52b}",
            if self.sign { '1' } else { '0' },
            self.raw_exp,
            self.frac
        )
    }
}

#[cfg(test)]
mod tests {
    use crate::Float64;
    use std::f64::consts::PI;

    #[test]
    fn mole() {
        assert_eq!(
            Float64::from(6.02214076e23).to_dec(),
            String::from("60221407600")
        );
    }

    #[test]
    fn border() {
        assert_eq!(Float64::from(1.0).to_dec(), String::from("1"));

        // max safe integer
        assert_eq!(
            Float64::from(9007199254740991.0).to_dec(),
            String::from("9007199254740991")
        );

        // exp would be 0x7ff
        assert_eq!(Float64::from(1.79e308).to_dec(), String::from("1.79e308"));

        assert_eq!(Float64::from(1.0 / 0.0).to_dec(), String::from("Infinity"));
        assert_eq!(Float64::from(0.0 / 0.0).to_dec(), String::from("NaN"));
    }

    #[test]
    fn pi() {
        assert_eq!(
            Float64::from(PI).to_dec(),
            String::from("3.1415926535897931")
        );
    }

    #[test]
    fn small() {
        assert_eq!(
            Float64::from(0.1 + 0.2).to_dec(),
            String::from("0.30000000000000004")
        );

        assert_eq!(Float64::from(1e-20).to_dec(), String::from("1e-20"));
    }

    #[test]
    fn three_hundred() {
        assert_eq!(Float64::from(300_f64).to_dec(), String::from("300"));
    }

    #[test]
    fn denormal() {
        assert_eq!(
            Float64::from(1.1754943367163553e-308).to_dec(),
            String::from("300")
        );

        assert_eq!(Float64::from(0.0).to_dec(), String::from("0"));
    }
}
