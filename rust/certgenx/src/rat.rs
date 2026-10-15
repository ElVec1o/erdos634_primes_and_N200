//! Exact rationals over `Int` (always normalised: gcd = 1, denominator > 0).
use crate::int::Int;
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Div, Mul, Neg, Sub};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Q {
    pub n: Int,
    pub d: Int,
}

impl Q {
    pub fn new(n: Int, d: Int) -> Q {
        assert!(!d.is_zero(), "zero denominator");
        let (mut n, mut d) = (n, d);
        if d.is_neg() {
            n = -n;
            d = -d;
        }
        if d == Int::one() {
            return Q { n, d };
        }
        let g = n.gcd(&d);
        if g != Int::one() && !g.is_zero() {
            n = n.div_exact(&g);
            d = d.div_exact(&g);
        }
        Q { n, d }
    }
    pub fn int(x: i64) -> Q {
        Q { n: Int::from_i64(x), d: Int::one() }
    }
    pub fn from_int(n: Int) -> Q {
        Q { n, d: Int::one() }
    }
    pub fn zero() -> Q {
        Q::int(0)
    }
    pub fn one() -> Q {
        Q::int(1)
    }
    pub fn is_zero(&self) -> bool {
        self.n.is_zero()
    }
    pub fn signum(&self) -> i32 {
        self.n.signum()
    }
    pub fn is_neg(&self) -> bool {
        self.n.is_neg()
    }
    pub fn is_pos(&self) -> bool {
        self.n.is_pos()
    }
    pub fn is_int(&self) -> bool {
        self.d == Int::one()
    }
    pub fn add_(&self, o: &Q) -> Q {
        if self.is_int() && o.is_int() {
            return Q { n: &self.n + &o.n, d: Int::one() };
        }
        Q::new(&self.n * &o.d + &o.n * &self.d, &self.d * &o.d)
    }
    pub fn sub_(&self, o: &Q) -> Q {
        if self.is_int() && o.is_int() {
            return Q { n: &self.n - &o.n, d: Int::one() };
        }
        Q::new(&self.n * &o.d - &o.n * &self.d, &self.d * &o.d)
    }
    pub fn mul_(&self, o: &Q) -> Q {
        if self.is_int() && o.is_int() {
            return Q { n: &self.n * &o.n, d: Int::one() };
        }
        Q::new(&self.n * &o.n, &self.d * &o.d)
    }
    pub fn div_(&self, o: &Q) -> Q {
        assert!(!o.is_zero(), "division by zero");
        Q::new(&self.n * &o.d, &self.d * &o.n)
    }
    pub fn neg_(&self) -> Q {
        Q { n: -&self.n, d: self.d.clone() }
    }
    pub fn parse(s: &str) -> Option<Q> {
        let s = s.trim();
        if let Some((a, b)) = s.split_once('/') {
            let d = Int::parse(b)?;
            if d.is_zero() {
                return None;
            }
            Some(Q::new(Int::parse(a)?, d))
        } else {
            Some(Q::from_int(Int::parse(s)?))
        }
    }
    /// sqrt of a nonnegative rational if it is rational
    pub fn sqrt_exact(&self) -> Option<Q> {
        if self.is_neg() {
            return None;
        }
        let (rn, rd) = (self.n.isqrt(), self.d.isqrt());
        if &rn * &rn != self.n || &rd * &rd != self.d {
            return None;
        }
        Some(Q::new(rn, rd))
    }
}
impl PartialOrd for Q {
    fn partial_cmp(&self, o: &Q) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Q {
    fn cmp(&self, o: &Q) -> Ordering {
        (&self.n * &o.d).cmp(&(&o.n * &self.d))
    }
}
impl fmt::Display for Q {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.is_int() { write!(f, "{}", self.n) } else { write!(f, "{}/{}", self.n, self.d) }
    }
}

macro_rules! fwdq {
    ($tr:ident, $m:ident, $impl:ident) => {
        impl<'a, 'b> $tr<&'b Q> for &'a Q {
            type Output = Q;
            fn $m(self, o: &'b Q) -> Q { self.$impl(o) }
        }
        impl $tr<Q> for Q {
            type Output = Q;
            fn $m(self, o: Q) -> Q { (&self).$impl(&o) }
        }
        impl<'b> $tr<&'b Q> for Q {
            type Output = Q;
            fn $m(self, o: &'b Q) -> Q { (&self).$impl(o) }
        }
        impl<'a> $tr<Q> for &'a Q {
            type Output = Q;
            fn $m(self, o: Q) -> Q { self.$impl(&o) }
        }
    };
}
fwdq!(Add, add, add_);
fwdq!(Sub, sub, sub_);
fwdq!(Mul, mul, mul_);
fwdq!(Div, div, div_);
impl Neg for Q {
    type Output = Q;
    fn neg(self) -> Q { self.neg_() }
}
impl<'a> Neg for &'a Q {
    type Output = Q;
    fn neg(self) -> Q { self.neg_() }
}
