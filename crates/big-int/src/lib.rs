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

        let mut idx = rhs.data.len() + offset;

        while carry {
            if self.data.len() == idx {
                self.data.push(1);
                carry = false
            } else {
                let (res, next_carry) = self.data[idx].carrying_add(0, carry);

                self.data[idx] = res;
                carry = next_carry;
                idx += 1;
            }
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

            let res = res / 2;

            if sign {
                rinf * 2 - &res
            } else {
                (false, rinf * 2 + &res)
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

    fn fft_mul(&mut self, rhs: &Self) {
        #[derive(Clone, Copy)]
        struct Complex {
            re: f64,
            im: f64,
        }

        impl Add<Self> for Complex {
            type Output = Self;

            fn add(self, rhs: Self) -> Self::Output {
                Self {
                    re: self.re + rhs.re,
                    im: self.im + rhs.im,
                }
            }
        }

        impl Sub<Self> for Complex {
            type Output = Self;

            fn sub(self, rhs: Self) -> Self::Output {
                Self {
                    re: self.re - rhs.re,
                    im: self.im - rhs.im,
                }
            }
        }

        impl Mul<Self> for Complex {
            type Output = Self;

            fn mul(self, rhs: Self) -> Self::Output {
                Self {
                    re: self.re * rhs.re - self.im * rhs.im,
                    im: self.im * rhs.re + self.re * rhs.im,
                }
            }
        }

        fn sort(data: &mut [Complex]) {
            let len = data.len();

            let mut step = 4;

            while step <= len {
                for i in 0..len / step {
                    for j in 0..step / 4 {
                        let idx = i * step + j + step / 4;

                        data.swap(idx, idx + step / 4);
                    }
                }

                step *= 2
            }
        }
        fn fft(data: &mut [Complex]) {
            if data.len() == 2 {
                let c0 = data[0];
                let c1 = data[1];

                data[0] = c0 + c1;
                data[1] = c0 - c1;
            } else {
                sort(data);
                let len = data.len();
                fft(&mut data[..len / 2]);
                fft(&mut data[len / 2..]);

                for k in 0..len / 2 {
                    let w = Complex {
                        re: (-2.0 * std::f64::consts::PI * k as f64 / len as f64).cos(),
                        im: (-2.0 * std::f64::consts::PI * k as f64 / len as f64).sin(),
                    };
                    let c0 = data[k];
                    let c1 = data[k + len / 2];
                    data[k] = c0 + w * c1;
                    data[k + len / 2] = c0 - w * c1;
                }
            }
        }

        fn ifft(data: &mut [Complex]) {
            if data.len() == 2 {
                let c0 = data[0];
                let c1 = data[1];

                data[0] = c0 + c1;
                data[1] = c0 - c1;
            } else {
                sort(data);
                let len = data.len();
                ifft(&mut data[..len / 2]);
                ifft(&mut data[len / 2..]);

                for k in 0..len / 2 {
                    let w = Complex {
                        re: (2.0 * std::f64::consts::PI * k as f64 / len as f64).cos(),
                        im: (2.0 * std::f64::consts::PI * k as f64 / len as f64).sin(),
                    };
                    let c0 = data[k];
                    let c1 = data[k + len / 2];
                    data[k] = c0 + w * c1;
                    data[k + len / 2] = c0 - w * c1;
                }
            }
        }

        let len = ((self.data.len() + rhs.data.len()) * 8).next_power_of_two();

        let mut a_cmp = vec![Complex { re: 0.0, im: 0.0 }; len];
        let mut b_cmp = vec![Complex { re: 0.0, im: 0.0 }; len];

        for (i, data) in self.data.iter().enumerate() {
            let mut data = *data;

            for j in 0..8 {
                a_cmp[i * 8 + j] = Complex {
                    re: (data % 256) as f64,
                    im: 0.0,
                };
                data = data / 256
            }
        }

        for (i, data) in rhs.data.iter().enumerate() {
            let mut data = *data;

            for j in 0..8 {
                b_cmp[i * 8 + j] = Complex {
                    re: (data % 256) as f64,
                    im: 0.0,
                };
                data = data / 256
            }
        }

        fft(&mut a_cmp);
        fft(&mut b_cmp);

        for (idx, b) in b_cmp.into_iter().enumerate() {
            a_cmp[idx] = a_cmp[idx] * b
        }

        ifft(&mut a_cmp);

        let mut res_data = Self::new();

        let mut carry = 0;

        for cmp in a_cmp.chunks(8) {
            let mut res: u64 = carry;
            let mut base = 1;
            let mut next_carry = 0;

            for idx in 0..8 {
                let cmp = cmp[idx];
                let re = cmp.re / len as f64;
                debug_assert!((re - re.round()).abs() < 1e-5);
                let re = re.round() as u64;
                debug_assert!(cmp.im.abs() < 1e-5);
                let (re, carry) = re.widening_mul(base);
                next_carry += carry;
                let (res_data, res_carry) = res.carrying_add(re, false);

                if res_carry {
                    next_carry += 1
                }

                res = res_data;

                if idx < 7 {
                    base *= 256;
                }
            }

            carry = next_carry;

            res_data.data.push(res)
        }

        res_data.trim();

        *self = res_data;
    }
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

        assert_eq!(a, a_clone);
    }

    #[test]
    fn took3_long() {
        let mut a = BigInt::try_from("12345678901234567890121234567890123456789012").unwrap();
        let mut a_clone = a.clone();
        let b = BigInt::try_from("987654321987654321098987654321987654321098").unwrap();

        a.toom3_mul(&b);

        a_clone.naive_mul(&b);

        assert_eq!(a, a_clone);
    }

    #[test]
    fn took3_very_long() {
        let mut a = BigInt::try_from("2372138972189327198373478927894543278954678564378564738564378567843657843657843657843657436543785647385674385674836543658743658473665784376856437856438568743123821093289089089090890890213980795843").unwrap();
        let mut a_clone = a.clone();
        let b = BigInt::try_from("3749832749823748932743289432789473289478932748932743289473289473289473289473298473294732984732987498237493278947329847329483289473249873289437289473249832792749239843298432987").unwrap();

        a.toom3_mul(&b);

        a_clone.naive_mul(&b);

        assert_eq!(a, a_clone);
    }

    #[test]
    fn fft() {
        let mut a = BigInt::try_from("12312321312312321").unwrap();
        let mut a_clone = a.clone();
        let b = BigInt::try_from("7897878978789789").unwrap();

        a.fft_mul(&b);
        a_clone.naive_mul(&b);

        assert_eq!(a, a_clone);
    }

    #[test]
    fn fft_long() {
        let mut a = BigInt::try_from("12345678901234567890121234567890123456789012").unwrap();
        let mut a_clone = a.clone();
        let b = BigInt::try_from("987654321987654321098987654321987654321098").unwrap();

        a.fft_mul(&b);

        a_clone.naive_mul(&b);

        assert_eq!(a, a_clone);
    }

    #[test]
    fn fft_very_long() {
        let mut a = BigInt::try_from("2372138972189327198373478927894543278954678564378564738564378567843657843657843657843657436543785647385674385674836543658743658473665784376856437856438568743123821093289089089090890890213980795843").unwrap();
        let mut a_clone = a.clone();
        let b = BigInt::try_from("3749832749823748932743289432789473289478932748932743289473289473289473289473298473294732984732987498237493278947329847329483289473249873289437289473249832792749239843298432987").unwrap();

        a.fft_mul(&b);

        a_clone.naive_mul(&b);

        assert_eq!(a, a_clone);
    }

    #[test]
    fn fft_quite_long() {
        let mut a = BigInt::try_from("23879213782187367845378876456783129783217657435456123673215362748731463217846347856479569472746335635263725136217463725467356743856794627958467856473895678436758642768215641254312312345677894974381986349746578467526423574521434251362173678684349569467523567846757542564567215342136472367988998678263726173267617456745674657386574354387564356512345676894723847821584675647825697456479356").unwrap();
        let mut a_clone = a.clone();
        let b = BigInt::try_from("9088945789457980243895463856483927849327543270543756856874654768904357890437508943785947389052789457804327905470824859067895482796789568754678321657321675312807943789543809547829057840923757854378924678547806782678321647863172478965984578947329858943275947235866852545273573214893057954398756621368731424681324632897980432780547908376543866748367834256776813768931").unwrap();

        a.fft_mul(&b);

        a_clone.naive_mul(&b);

        assert_eq!(a, a_clone);
    }
}
