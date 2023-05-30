use std::{
    fmt::Display,
    iter::Sum,
    ops::{Add, AddAssign, Div, Mul, Neg, Rem, Sub},
};

use num_rational::Rational64;
use num_traits::{Bounded, Num, One, Signed, Zero};

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Credit(Rational64);

impl Display for Credit {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.0)
    }
}

impl Credit {
    #[inline]
    pub fn from_integer(integer: i64) -> Self {
        Credit(Rational64::from_integer(integer))
    }

    pub fn new(numer: i64, denom: i64) -> Self {
        Credit(Rational64::new(numer, denom))
    }
}

impl Add for Credit {
    type Output = Credit;

    fn add(self, rhs: Self) -> Self::Output {
        Credit(self.0 + rhs.0)
    }
}

impl AddAssign for Credit {
    fn add_assign(&mut self, rhs: Self) {
        self.0 += rhs.0
    }
}

impl Sub for Credit {
    type Output = Credit;

    fn sub(self, rhs: Self) -> Self::Output {
        Credit(self.0 - rhs.0)
    }
}

impl Div for Credit {
    type Output = Credit;

    fn div(self, rhs: Self) -> Self::Output {
        Credit(self.0 / rhs.0)
    }
}

impl Rem for Credit {
    type Output = Credit;

    fn rem(self, rhs: Self) -> Self::Output {
        Credit(self.0 % rhs.0)
    }
}

impl Mul for Credit {
    type Output = Credit;

    fn mul(self, rhs: Self) -> Self::Output {
        Credit(self.0 * rhs.0)
    }
}

impl From<Rational64> for Credit {
    fn from(value: Rational64) -> Self {
        Credit(value)
    }
}

impl Sum for Credit {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Credit(iter.map(|e| e.0).sum())
    }
}

impl Bounded for Credit {
    fn min_value() -> Self {
        Credit::from_integer(-10000)
    }

    fn max_value() -> Self {
        Credit::from_integer(10000)
    }
}

impl One for Credit {
    fn one() -> Self {
        Credit::from_integer(1)
    }
}

impl Zero for Credit {
    fn zero() -> Self {
        Credit::from_integer(0)
    }

    fn is_zero(&self) -> bool {
        self.0.is_zero()
    }
}

impl Num for Credit {
    type FromStrRadixErr = <Rational64 as Num>::FromStrRadixErr;

    fn from_str_radix(str: &str, radix: u32) -> Result<Self, Self::FromStrRadixErr> {
        Rational64::from_str_radix(str, radix).map(Credit)
    }
}

impl Signed for Credit {
    fn abs(&self) -> Self {
        Credit(self.0.abs())
    }

    fn abs_sub(&self, other: &Self) -> Self {
        Credit(self.0.abs_sub(&other.0))
    }

    fn signum(&self) -> Self {
        Credit(self.0.signum())
    }

    fn is_positive(&self) -> bool {
        self.0.is_positive()
    }

    fn is_negative(&self) -> bool {
        self.0.is_negative()
    }
}

impl Neg for Credit {
    type Output = Credit;

    fn neg(self) -> Self::Output {
        Credit(-self.0)
    }
}

#[derive(Clone, Debug)]
pub struct CreditInv {
    pub c: Credit,
}

impl CreditInv {
    pub fn new(c: Credit) -> Self {
        CreditInv { c }
    }
}

impl CreditInv {
    pub fn two_ec_credit(&self, num_edges: usize) -> Credit {
        (self.c * Credit::from_integer(num_edges as i64)).min(self.large())
    }

    pub fn complex_comp(&self) -> Credit {
        (Credit::from_integer(13) * self.c) - Credit::from_integer(2)
    }

    pub fn complex_black(&self, deg: i64) -> Credit {
        Credit::from_integer(deg) * self.c * Credit::new(1, 2)
    }

    pub fn complex_block(&self) -> Credit {
        Credit::from_integer(1)
    }

    pub fn large(&self) -> Credit {
        Credit::from_integer(2)
        //self.c * Credit::from_integer(6)
    }
}

impl Display for CreditInv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Credit Scheme with c = {}", self.c)
    }
}
