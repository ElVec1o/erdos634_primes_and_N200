//! Exact integers: i128 fast path with checked arithmetic, automatic promotion to a small
//! sign-magnitude bignum on overflow.  Never wraps.  `PROMOTIONS` counts slow-path operations.
use std::cmp::Ordering;
use std::fmt;
use std::ops::{Add, Mul, Neg, Sub};
use std::sync::atomic::{AtomicUsize, Ordering as AO};

pub static PROMOTIONS: AtomicUsize = AtomicUsize::new(0);

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Big {
    neg: bool,
    mag: Vec<u32>, // little endian, no trailing zeros; zero = empty
}

/// Invariant: `B` is used only for values that do not fit in i128 (so structural equality is value equality).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Int {
    S(i128),
    B(Big),
}

fn trim(v: &mut Vec<u32>) {
    while let Some(&0) = v.last() {
        v.pop();
    }
}
fn mag_from_u128(mut u: u128) -> Vec<u32> {
    let mut v = Vec::new();
    while u > 0 {
        v.push(u as u32);
        u >>= 32;
    }
    v
}
fn mag_cmp(a: &[u32], b: &[u32]) -> Ordering {
    if a.len() != b.len() {
        return a.len().cmp(&b.len());
    }
    for i in (0..a.len()).rev() {
        if a[i] != b[i] {
            return a[i].cmp(&b[i]);
        }
    }
    Ordering::Equal
}
fn mag_add(a: &[u32], b: &[u32]) -> Vec<u32> {
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let mut r = Vec::with_capacity(a.len() + 1);
    let mut c = 0u64;
    for i in 0..a.len() {
        let s = a[i] as u64 + if i < b.len() { b[i] as u64 } else { 0 } + c;
        r.push(s as u32);
        c = s >> 32;
    }
    if c > 0 {
        r.push(c as u32);
    }
    r
}
fn mag_sub(a: &[u32], b: &[u32]) -> Vec<u32> {
    // requires a >= b
    let mut r = Vec::with_capacity(a.len());
    let mut borrow = 0i64;
    for i in 0..a.len() {
        let mut d = a[i] as i64 - borrow - if i < b.len() { b[i] as i64 } else { 0 };
        if d < 0 {
            d += 1 << 32;
            borrow = 1;
        } else {
            borrow = 0;
        }
        r.push(d as u32);
    }
    assert!(borrow == 0);
    trim(&mut r);
    r
}
fn mag_mul(a: &[u32], b: &[u32]) -> Vec<u32> {
    if a.is_empty() || b.is_empty() {
        return vec![];
    }
    let mut r = vec![0u32; a.len() + b.len()];
    for i in 0..a.len() {
        let mut c = 0u64;
        for j in 0..b.len() {
            let t = a[i] as u64 * b[j] as u64 + r[i + j] as u64 + c;
            r[i + j] = t as u32;
            c = t >> 32;
        }
        r[i + b.len()] = c as u32;
    }
    trim(&mut r);
    r
}
fn mag_divrem_small(a: &[u32], d: u32) -> (Vec<u32>, u32) {
    let mut q = vec![0u32; a.len()];
    let mut r = 0u64;
    for i in (0..a.len()).rev() {
        let cur = (r << 32) | a[i] as u64;
        q[i] = (cur / d as u64) as u32;
        r = cur % d as u64;
    }
    trim(&mut q);
    (q, r as u32)
}
fn shl1(r: &mut Vec<u32>) {
    let mut c = 0u32;
    for x in r.iter_mut() {
        let n = (*x >> 31) & 1;
        *x = (*x << 1) | c;
        c = n;
    }
    if c > 0 {
        r.push(c);
    }
}
fn mag_divrem(a: &[u32], b: &[u32]) -> (Vec<u32>, Vec<u32>) {
    assert!(!b.is_empty(), "division by zero");
    if mag_cmp(a, b) == Ordering::Less {
        return (vec![], a.to_vec());
    }
    if b.len() == 1 {
        let (q, r) = mag_divrem_small(a, b[0]);
        return (q, if r == 0 { vec![] } else { vec![r] });
    }
    let nbits = a.len() * 32;
    let mut q = vec![0u32; a.len()];
    let mut r: Vec<u32> = Vec::new();
    for i in (0..nbits).rev() {
        shl1(&mut r);
        if (a[i / 32] >> (i % 32)) & 1 == 1 {
            if r.is_empty() {
                r.push(1)
            } else {
                r[0] |= 1
            }
        }
        if mag_cmp(&r, b) != Ordering::Less {
            r = mag_sub(&r, b);
            q[i / 32] |= 1 << (i % 32);
        }
    }
    trim(&mut q);
    (q, r)
}

impl Big {
    fn from_i128(x: i128) -> Big {
        Big { neg: x < 0, mag: mag_from_u128(x.unsigned_abs()) }
    }
    fn norm(self) -> Int {
        if self.mag.len() <= 4 {
            let mut u = 0u128;
            for (i, w) in self.mag.iter().enumerate() {
                u |= (*w as u128) << (32 * i);
            }
            if !self.neg && u <= i128::MAX as u128 {
                return Int::S(u as i128);
            }
            if self.neg && u <= (i128::MAX as u128) + 1 {
                return Int::S((u as i128).wrapping_neg()); // u == 2^127 wraps to MIN, whose negation is MIN: correct
            }
        }
        Int::B(self)
    }
    fn add(&self, o: &Big) -> Big {
        if self.neg == o.neg {
            Big { neg: self.neg, mag: mag_add(&self.mag, &o.mag) }
        } else {
            match mag_cmp(&self.mag, &o.mag) {
                Ordering::Equal => Big { neg: false, mag: vec![] },
                Ordering::Greater => Big { neg: self.neg, mag: mag_sub(&self.mag, &o.mag) },
                Ordering::Less => Big { neg: o.neg, mag: mag_sub(&o.mag, &self.mag) },
            }
        }
    }
    fn negate(&self) -> Big {
        Big { neg: !self.neg && !self.mag.is_empty(), mag: self.mag.clone() }
    }
}

impl Int {
    pub fn from_i64(x: i64) -> Int {
        Int::S(x as i128)
    }
    pub fn zero() -> Int {
        Int::S(0)
    }
    pub fn one() -> Int {
        Int::S(1)
    }
    fn from_u128(u: u128) -> Int {
        if u <= i128::MAX as u128 {
            Int::S(u as i128)
        } else {
            PROMOTIONS.fetch_add(1, AO::Relaxed);
            Int::B(Big { neg: false, mag: mag_from_u128(u) })
        }
    }
    fn to_big(&self) -> Big {
        match self {
            Int::S(x) => Big::from_i128(*x),
            Int::B(b) => b.clone(),
        }
    }
    pub fn is_zero(&self) -> bool {
        matches!(self, Int::S(0))
    }
    pub fn signum(&self) -> i32 {
        match self {
            Int::S(x) => (*x > 0) as i32 - (*x < 0) as i32,
            Int::B(b) => {
                if b.neg {
                    -1
                } else {
                    1
                }
            }
        }
    }
    pub fn is_neg(&self) -> bool {
        self.signum() < 0
    }
    pub fn is_pos(&self) -> bool {
        self.signum() > 0
    }
    pub fn abs(&self) -> Int {
        if self.is_neg() {
            -self
        } else {
            self.clone()
        }
    }
    pub fn as_i64(&self) -> Option<i64> {
        match self {
            Int::S(x) => i64::try_from(*x).ok(),
            _ => None,
        }
    }
    pub fn add_(&self, o: &Int) -> Int {
        if let (Int::S(a), Int::S(b)) = (self, o) {
            if let Some(r) = a.checked_add(*b) {
                return Int::S(r);
            }
        }
        PROMOTIONS.fetch_add(1, AO::Relaxed);
        self.to_big().add(&o.to_big()).norm()
    }
    pub fn neg_(&self) -> Int {
        if let Int::S(a) = self {
            if let Some(r) = a.checked_neg() {
                return Int::S(r);
            }
        }
        PROMOTIONS.fetch_add(1, AO::Relaxed);
        self.to_big().negate().norm()
    }
    pub fn sub_(&self, o: &Int) -> Int {
        if let (Int::S(a), Int::S(b)) = (self, o) {
            if let Some(r) = a.checked_sub(*b) {
                return Int::S(r);
            }
        }
        PROMOTIONS.fetch_add(1, AO::Relaxed);
        self.to_big().add(&o.to_big().negate()).norm()
    }
    pub fn mul_(&self, o: &Int) -> Int {
        if let (Int::S(a), Int::S(b)) = (self, o) {
            if let Some(r) = a.checked_mul(*b) {
                return Int::S(r);
            }
        }
        PROMOTIONS.fetch_add(1, AO::Relaxed);
        let (x, y) = (self.to_big(), o.to_big());
        let mag = mag_mul(&x.mag, &y.mag);
        let neg = (x.neg != y.neg) && !mag.is_empty();
        Big { neg, mag }.norm()
    }
    /// truncating division with remainder (sign of remainder = sign of dividend)
    pub fn divrem(&self, o: &Int) -> (Int, Int) {
        assert!(!o.is_zero(), "division by zero");
        if let (Int::S(a), Int::S(b)) = (self, o) {
            if let (Some(q), Some(r)) = (a.checked_div(*b), a.checked_rem(*b)) {
                return (Int::S(q), Int::S(r));
            }
        }
        PROMOTIONS.fetch_add(1, AO::Relaxed);
        let (x, y) = (self.to_big(), o.to_big());
        let (q, r) = mag_divrem(&x.mag, &y.mag);
        let qn = (x.neg != y.neg) && !q.is_empty();
        let rn = x.neg && !r.is_empty();
        (Big { neg: qn, mag: q }.norm(), Big { neg: rn, mag: r }.norm())
    }
    pub fn div_exact(&self, o: &Int) -> Int {
        let (q, r) = self.divrem(o);
        assert!(r.is_zero(), "inexact division");
        q
    }
    pub fn gcd(&self, o: &Int) -> Int {
        if let (Int::S(a), Int::S(b)) = (self, o) {
            let (mut x, mut y) = (a.unsigned_abs(), b.unsigned_abs());
            while y != 0 {
                let t = x % y;
                x = y;
                y = t;
            }
            return Int::from_u128(x);
        }
        let (mut x, mut y) = (self.abs(), o.abs());
        while !y.is_zero() {
            let (_, r) = x.divrem(&y);
            x = y;
            y = r;
        }
        x
    }
    pub fn lcm(&self, o: &Int) -> Int {
        let g = self.gcd(o);
        self.mul_(o).div_exact(&g).abs()
    }
    pub fn min(&self, o: &Int) -> Int {
        if self <= o { self.clone() } else { o.clone() }
    }
    pub fn max(&self, o: &Int) -> Int {
        if self >= o { self.clone() } else { o.clone() }
    }
    /// floor(sqrt(n)) for n >= 0
    pub fn isqrt(&self) -> Int {
        assert!(!self.is_neg());
        if self.is_zero() {
            return Int::zero();
        }
        let mut x = match self {
            Int::S(n) => {
                let e = (*n as f64).sqrt() as i128;
                Int::S(e * 2 + 2)
            }
            _ => self.clone(),
        };
        loop {
            let y = x.add_(&self.divrem(&x).0).div_exact_floor2();
            if y >= x {
                return x;
            }
            x = y;
        }
    }
    fn div_exact_floor2(&self) -> Int {
        self.divrem(&Int::S(2)).0
    }
    pub fn parse(s: &str) -> Option<Int> {
        let s = s.trim();
        let (neg, digits) = match s.strip_prefix('-') {
            Some(r) => (true, r),
            None => (false, s.strip_prefix('+').unwrap_or(s)),
        };
        if digits.is_empty() || !digits.bytes().all(|c| c.is_ascii_digit()) {
            return None;
        }
        let mut r = Int::zero();
        let ten = Int::S(10);
        for c in digits.bytes() {
            r = r.mul_(&ten).add_(&Int::S((c - b'0') as i128));
        }
        Some(if neg { r.neg_() } else { r })
    }
}

impl PartialOrd for Int {
    fn partial_cmp(&self, o: &Int) -> Option<Ordering> {
        Some(self.cmp(o))
    }
}
impl Ord for Int {
    fn cmp(&self, o: &Int) -> Ordering {
        match (self, o) {
            (Int::S(a), Int::S(b)) => a.cmp(b),
            (Int::S(_), Int::B(b)) => if b.neg { Ordering::Greater } else { Ordering::Less },
            (Int::B(a), Int::S(_)) => if a.neg { Ordering::Less } else { Ordering::Greater },
            (Int::B(a), Int::B(b)) => match (a.neg, b.neg) {
                (false, true) => Ordering::Greater,
                (true, false) => Ordering::Less,
                (false, false) => mag_cmp(&a.mag, &b.mag),
                (true, true) => mag_cmp(&b.mag, &a.mag),
            },
        }
    }
}
impl fmt::Display for Int {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            Int::S(x) => write!(f, "{}", x),
            Int::B(b) => {
                let mut parts = Vec::new();
                let mut m = b.mag.clone();
                while !m.is_empty() {
                    let (q, r) = mag_divrem_small(&m, 1_000_000_000);
                    parts.push(r);
                    m = q;
                }
                let mut s = String::new();
                if b.neg {
                    s.push('-');
                }
                s.push_str(&parts.pop().unwrap().to_string());
                while let Some(p) = parts.pop() {
                    s.push_str(&format!("{:09}", p));
                }
                write!(f, "{}", s)
            }
        }
    }
}

macro_rules! fwd {
    ($tr:ident, $m:ident, $impl:ident) => {
        impl<'a, 'b> $tr<&'b Int> for &'a Int {
            type Output = Int;
            fn $m(self, o: &'b Int) -> Int { self.$impl(o) }
        }
        impl $tr<Int> for Int {
            type Output = Int;
            fn $m(self, o: Int) -> Int { (&self).$impl(&o) }
        }
        impl<'b> $tr<&'b Int> for Int {
            type Output = Int;
            fn $m(self, o: &'b Int) -> Int { (&self).$impl(o) }
        }
        impl<'a> $tr<Int> for &'a Int {
            type Output = Int;
            fn $m(self, o: Int) -> Int { self.$impl(&o) }
        }
    };
}
fwd!(Add, add, add_);
fwd!(Sub, sub, sub_);
fwd!(Mul, mul, mul_);
impl Neg for Int {
    type Output = Int;
    fn neg(self) -> Int { self.neg_() }
}
impl<'a> Neg for &'a Int {
    type Output = Int;
    fn neg(self) -> Int { self.neg_() }
}
impl From<i64> for Int {
    fn from(x: i64) -> Int { Int::S(x as i128) }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn big_arith() {
        let a = Int::parse("123456789012345678901234567890123456789012345678901234567890").unwrap();
        let b = Int::parse("-987654321098765432109876543210987654321").unwrap();
        let p = &a * &b;
        assert_eq!(p.divrem(&b).0, a);
        assert_eq!(p.divrem(&a).0, b);
        assert_eq!(a.to_string(), "123456789012345678901234567890123456789012345678901234567890");
        assert_eq!((&p + &(-&p)), Int::zero());
        let s = Int::parse("1000000000000000000000000000000000000000000000000").unwrap().isqrt();
        assert_eq!(s.to_string(), "1000000000000000000000000");
        assert_eq!(Int::S(i128::MAX).add_(&Int::one()).sub_(&Int::one()), Int::S(i128::MAX));
        assert_eq!(Int::S(i128::MIN).neg_().neg_(), Int::S(i128::MIN));
        assert_eq!(Int::S(12).gcd(&Int::S(-18)), Int::S(6));
        assert_eq!(Int::S(99).isqrt(), Int::S(9));
    }
}
