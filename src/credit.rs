use std::fmt::Display;

use num_rational::Rational64;

pub type Credit = Rational64;

#[derive(Clone, Debug)]
pub struct CreditInv {
    pub c: Rational64,
}

impl CreditInv {
    pub fn new(c: Rational64) -> Self {
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
        //Credit::from_integer(2)
        self.c * Credit::from_integer(6)
    }
}

impl Display for CreditInv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Credit Scheme with c = {}", self.c)
    }
}
