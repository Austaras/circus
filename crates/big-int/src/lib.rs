#![feature(ascii_char)]
#![feature(ascii_char_variants)]
#![feature(bigint_helper_methods)]
use std::ascii::Char;
use std::cmp::Ordering;
use std::fmt::Display;
use std::ops::{Add, AddAssign, Div, Mul, MulAssign, Sub};

#[derive(PartialEq, Eq, Clone, Debug)]
pub struct BigInt {
    data: Vec<u64>,
}

impl PartialOrd for BigInt {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        match self.data.len().cmp(&other.data.len()) {
            Ordering::Less => Some(Ordering::Less),
            Ordering::Equal => {
                for (this, other) in self.data.iter().zip(other.data.iter()).rev() {
                    match this.cmp(other) {
                        Ordering::Less => return Some(Ordering::Less),
                        Ordering::Equal => continue,
                        Ordering::Greater => return Some(Ordering::Greater),
                    }
                }

                Some(Ordering::Equal)
            }
            Ordering::Greater => Some(Ordering::Greater),
        }
    }
}

#[derive(Debug)]
pub enum ParseBigIntError {
    NonAscii,
    InValidAscii(Char),
}

impl BigInt {
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    fn from_slice(slice: &[u64]) -> Self {
        if slice.is_empty() {
            Self::from(0)
        } else {
            Self {
                data: slice.to_owned(),
            }
        }
    }

    fn trim(&mut self) {
        while self.data.last() == Some(&0) && !self.data.is_empty() {
            self.data.pop();
        }
    }

    fn add_with_offset(&mut self, rhs: &Self, offset: usize) {
        let mut carry = false;

        while self.data.len() < rhs.data.len() + offset {
            self.data.push(0)
        }

        for (idx, value) in rhs.data.iter().enumerate() {
            let (res, next_carry) = value.carrying_add(self.data[idx + offset], carry);

            carry = next_carry;

            self.data[idx + offset] = res;
        }

        if carry {
            self.data.push(1)
        }
    }

    fn single_div_rem(&mut self, rhs: u64) -> u64 {
        let mut remain = 0;

        for data in self.data.iter_mut().rev() {
            if remain == 0 {
                let q = *data / rhs;
                let r = *data % rhs;

                *data = q;
                remain = r;
            } else {
                let mut start = *data / rhs;
                let mut end = std::u64::MAX;
                let mut q = start / 2 + end / 2;

                loop {
                    let (low, high) = q.widening_mul(rhs);

                    if high == remain && low <= *data && *data - low < rhs {
                        remain = *data - low;
                        *data = q;
                        break;
                    } else if high > remain || (high == remain && low > *data) {
                        end = q;
                        let extra = if q % 2 == 1 && start % 2 == 1 { 1 } else { 0 };
                        q = q / 2 + start / 2 + extra;
                    } else {
                        start = q;
                        let extra = if q % 2 == 1 && end % 2 == 1 { 1 } else { 0 };
                        q = q / 2 + end / 2 + extra;
                    }
                }
            }
        }

        self.trim();

        remain
    }

    fn naive_mul(&mut self, rhs: &Self) {
        let mut res = Self::new();

        for (idx, rhs) in rhs.data.iter().enumerate() {
            let mut curr = Self::new();

            for _ in 0..idx {
                curr.data.push(0)
            }

            for num in &self.data {
                curr.data.push(*num)
            }

            curr = curr * *rhs;

            res += &curr;
        }

        *self = res;
    }

    fn toom3_mul(&mut self, rhs: &Self) {
        let len = (self.data.len().max(rhs.data.len()) / 3).max(1);
        let m0 = Self::from_slice(&self.data[..len]);
        let m1 = Self::from_slice(&self.data[len..len * 2]);
        let m2 = Self::from_slice(&self.data[len * 2..]);

        let n0 = Self::from_slice(&rhs.data[..len]);
        let n1 = Self::from_slice(&rhs.data[len..len * 2]);
        let n2 = Self::from_slice(&rhs.data[len * 2..]);

        let p = m0.clone() + &m2;
        let p0 = m0.clone();
        let p1 = p.clone() + &m1;
        let (pneg1_sign, pneg1) = p.clone() - &m1;
        let (pneg2_sign, pneg2) = {
            let (sign, p) = if pneg1_sign {
                m2.clone() - &pneg1
            } else {
                (false, m2.clone() + &pneg1)
            };
            let p = p * 2;

            if sign {
                (true, p + &m0)
            } else {
                p - &m0
            }
        };
        let pinf = m2;

        let q = n0.clone() + &n2;
        let q0 = n0.clone();
        let q1 = q.clone() + &n1;
        let (qneg1_sign, qneg1) = q.clone() - &n1;
        let (qneg2_sign, qneg2) = {
            let (sign, q) = if qneg1_sign {
                n2.clone() - &qneg1
            } else {
                (false, n2.clone() + &qneg1)
            };
            let q = q * 2;

            if sign {
                (true, q + &n0)
            } else {
                q - &n0
            }
        };
        let qinf = n2;

        let r0 = p0 * &q0;
        let r1 = p1 * &q1;
        let rneg1_sign = pneg1_sign ^ qneg1_sign;
        let rneg1 = pneg1 * &qneg1;
        let rneg2_sign = pneg2_sign ^ qneg2_sign;
        let rneg2 = pneg2 * &qneg2;
        let rinf = pinf * &qinf;

        let res0 = r0.clone();
        let res4 = rinf.clone();
        let (mut res3_sign, mut res3) = {
            let (sign, res) = if rneg2_sign {
                (true, rneg2 + &r1)
            } else {
                rneg2 - &r1
            };

            (sign, res / 3)
        };
        let (mut res1_sign, mut res1) = {
            let (sign, res) = if rneg1_sign {
                (false, r1 + &rneg1)
            } else {
                r1 - &rneg1
            };

            (sign, res / 2)
        };
        let (mut res2_sign, mut res2) = if rneg1_sign {
            (true, rneg1 + &r0)
        } else {
            rneg1 - &r0
        };
        (res3_sign, res3) = {
            let (sign, res) = match (res2_sign, res3_sign) {
                (true, true) => res3.clone() - &res2,
                (true, false) => (true, res2.clone() + &res3),
                (false, true) => (false, res2.clone() + &res3),
                (false, false) => res2.clone() - &res3,
            };

            if sign {
                rinf - &res
            } else {
                (false, rinf + &res)
            }
        };
        (res2_sign, res2) = {
            let (sign, res) = if res2_sign {
                res1.clone() - &res2
            } else {
                (false, res1.clone() + &res2)
            };

            if sign {
                (true, res + &res4)
            } else {
                res - &res4
            }
        };
        (res1_sign, res1) = match (res1_sign, res3_sign) {
            (true, true) => res3.clone() - &res1,
            (true, false) => (true, res1 + &res3),
            (false, true) => (false, res1 + &res3),
            (false, false) => res1 - &res3,
        };

        debug_assert!(!res1_sign);
        debug_assert!(!res2_sign);
        debug_assert!(!res3_sign);

        let mut res = res0;

        res.add_with_offset(&res1, len * 1);
        res.add_with_offset(&res2, len * 2);
        res.add_with_offset(&res3, len * 3);
        res.add_with_offset(&res4, len * 4);

        res.trim();

        *self = res;
    }

    fn fft_mul(&mut self, rhs: &Self) {}
}

impl AddAssign<&Self> for BigInt {
    fn add_assign(&mut self, rhs: &Self) {
        self.add_with_offset(rhs, 0);
    }
}

impl Add<&Self> for BigInt {
    type Output = Self;

    fn add(mut self, rhs: &Self) -> Self::Output {
        self += rhs;

        self
    }
}

impl Sub<&Self> for BigInt {
    type Output = (bool, Self);

    fn sub(mut self, rhs: &Self) -> Self::Output {
        if &self > rhs {
            let mut borrow = false;

            for (idx, rhs) in rhs.data.iter().enumerate() {
                let (data, next) = self.data[idx].borrowing_sub(*rhs, borrow);

                self.data[idx] = data;
                borrow = next
            }

            if borrow {
                let len = rhs.data.len();

                self.data[len] -= 1;
            }

            self.trim();

            (false, self)
        } else {
            let mut res = rhs.clone();

            let mut borrow = false;

            for (idx, rhs) in self.data.iter().enumerate() {
                let (data, next) = res.data[idx].borrowing_sub(*rhs, borrow);

                res.data[idx] = data;
                borrow = next
            }

            if borrow {
                let len = self.data.len();

                res.data[len] -= 1;
            }

            res.trim();

            (true, res)
        }
    }
}

impl MulAssign<&Self> for BigInt {
    fn mul_assign(&mut self, rhs: &Self) {
        if self.data.len() < 10 || rhs.data.len() < 10 {
            self.naive_mul(rhs);
        } else if self.data.len() > 100 && self.data.len() > 100 {
            self.fft_mul(rhs);
        } else {
            self.toom3_mul(rhs);
        }
    }
}

impl Mul<&Self> for BigInt {
    type Output = Self;

    fn mul(mut self, rhs: &Self) -> Self::Output {
        self *= rhs;

        self
    }
}

impl Mul<u64> for BigInt {
    type Output = Self;

    fn mul(mut self, rhs: u64) -> Self::Output {
        let mut carry = 0;

        for idx in 0..self.data.len() {
            let lhs = self.data[idx];

            let (res, next_carry) = lhs.carrying_mul(rhs, carry);

            self.data[idx] = res;
            carry = next_carry;
        }

        if carry > 0 {
            self.data.push(carry)
        }

        self
    }
}

impl Div<u64> for BigInt {
    type Output = Self;

    fn div(mut self, rhs: u64) -> Self::Output {
        self.single_div_rem(rhs);

        self
    }
}

impl Display for BigInt {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut res = Vec::new();
        let mut temp = self.clone();

        while temp.data.len() > 1 {
            res.push(temp.single_div_rem(10) as u8)
        }

        temp.data[0].fmt(f)?;

        for digit in res.iter().rev() {
            digit.fmt(f)?;
        }

        Ok(())
    }
}

impl From<u64> for BigInt {
    fn from(value: u64) -> Self {
        Self { data: vec![value] }
    }
}

impl<'a> TryFrom<&'a str> for BigInt {
    type Error = ParseBigIntError;

    fn try_from(value: &str) -> Result<Self, Self::Error> {
        let Some(ascii) = value.as_ascii() else {
            return Err(ParseBigIntError::NonAscii);
        };

        let ten = BigInt { data: vec![10] };
        let mut base = BigInt { data: vec![1] };
        let mut res = BigInt::new();

        for char in ascii.iter().rev() {
            let digit: u64 = match char {
                Char::Digit0 => 0,
                Char::Digit1 => 1,
                Char::Digit2 => 2,
                Char::Digit3 => 3,
                Char::Digit4 => 4,
                Char::Digit5 => 5,
                Char::Digit6 => 6,
                Char::Digit7 => 7,
                Char::Digit8 => 8,
                Char::Digit9 => 9,
                c => return Err(ParseBigIntError::InValidAscii(*c)),
            };

            let digit = BigInt { data: vec![digit] };
            let curr = digit * &base;
            res += &curr;
            base *= &ten;
        }

        Ok(res)
    }
}

#[cfg(test)]
mod tests {
    use crate::BigInt;

    #[test]
    fn basic_add() {
        let a = BigInt {
            data: vec![
                18446744073709551516,
                5432112345678,
                90987654321,
                348932489320432,
            ],
        };
        let b = BigInt {
            data: vec![9999888777, 666555444333, 2221110009998],
        };

        let res = a + &b;

        assert_eq!(
            res,
            BigInt {
                data: vec![9999888677, 6098667790012, 2312097664319, 348932489320432]
            }
        );
    }

    #[test]
    fn basic_mul() {
        let mut a = BigInt {
            data: vec![321321312321321, 3211321321, 432432423],
        };
        let b = BigInt {
            data: vec![9999888777, 666555444333, 2221110009998],
        };

        a.naive_mul(&b);

        assert_eq!(
            a,
            BigInt {
                data: vec![
                    12821669717727929841,
                    16055625829368169872,
                    14517504970175516129,
                    5346999618660315912,
                    1249291540092681524,
                    52
                ]
            }
        )
    }

    #[test]
    fn parse() {
        let a = BigInt::try_from("12345678909876543211234567890987654321").unwrap();
        let b = BigInt::try_from("111122223333444556576778888999000").unwrap();

        let res = a * &b;

        assert_eq!(
            res.to_string(),
            "1371879289026297566931018689952872557593800222895024280091441714679000"
        )
    }

    #[test]
    fn single_div() {
        let a = BigInt::try_from("12321321321312312344354354354312").unwrap();

        assert_eq!((a / 7).to_string(), "1760188760187473192050622050616");

        let a = BigInt::try_from("83724932879432789438924732894798423978").unwrap();

        assert_eq!(
            (a / 4).to_string(),
            "20931233219858197359731183223699605994"
        )
    }

    #[test]
    fn took3_simple() {
        let mut a = BigInt::try_from("1234567890123456789012").unwrap();
        let mut a_clone = a.clone();
        let b = BigInt::try_from("987654321987654321098").unwrap();

        a.toom3_mul(&b);

        a_clone.naive_mul(&b);
    }
}
