//! Exact rational arithmetic on i128 (the field Q), points (X, Y*sqrt(D)) and unit directions (c, s*sqrt(D)).
//! Overflow is a hard error (panic with a message), never a silent wrap: `overflow-checks = true` in the release profile
//! plus checked operations below.  (BigRational fallback is milestone M1b; no witness or benchmark needed it.)
use std::cmp::Ordering;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Q { pub n: i128, pub d: i128 } // d > 0, gcd(n,d) = 1

fn gcd_u(mut a: u128, mut b: u128) -> u128 {
    if a == 0 { return b; }
    if b == 0 { return a; }
    let sh = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop {
        b >>= b.trailing_zeros();
        if a > b { std::mem::swap(&mut a, &mut b); }
        b -= a;
        if b == 0 { break; }
    }
    a << sh
}
#[inline] fn gcd64(mut a: u64, mut b: u64) -> u64 {
    if a == 0 { return b; }
    if b == 0 { return a; }
    let sh = (a | b).trailing_zeros();
    a >>= a.trailing_zeros();
    loop { b >>= b.trailing_zeros(); if a > b { std::mem::swap(&mut a, &mut b); } b -= a; if b == 0 { break; } }
    a << sh
}
#[inline] pub fn gcd(a: i128, b: i128) -> i128 {
    let (a, b) = (a.unsigned_abs(), b.unsigned_abs());
    if (a | b) >> 64 == 0 { gcd64(a as u64, b as u64) as i128 } else { gcd_u(a, b) as i128 }
}
#[inline] fn mulc(a: i128, b: i128) -> i128 { a.checked_mul(b).unwrap_or_else(|| panic!("Q overflow in mul {} * {}", a, b)) }
#[inline] fn addc(a: i128, b: i128) -> i128 { a.checked_add(b).unwrap_or_else(|| panic!("Q overflow in add")) }

const SM: i128 = 1 << 30;
#[inline] fn small(a: &Q) -> bool { a.n > -SM && a.n < SM && a.d < SM }
impl Q {
    #[inline] fn norm64(n: i64, d: i64) -> Q {
        if d == 1 { return Q { n: n as i128, d: 1 }; }
        let g = gcd64(n.unsigned_abs(), d as u64) as i64;
        if g == 1 { Q { n: n as i128, d: d as i128 } } else { Q { n: (n / g) as i128, d: (d / g) as i128 } }
    }
    pub const ZERO: Q = Q { n: 0, d: 1 };
    pub const ONE: Q = Q { n: 1, d: 1 };
    #[inline] pub fn int(n: i128) -> Q { Q { n, d: 1 } }
    #[inline] pub fn new(n: i128, d: i128) -> Q {
        assert!(d != 0, "Q division by zero");
        let (mut n, mut d) = if d < 0 { (-n, -d) } else { (n, d) };
        if d == 1 { return Q { n, d }; }
        let g = gcd(n, d);
        if g > 1 { n /= g; d /= g; }
        Q { n, d }
    }
    #[inline] pub fn is_zero(&self) -> bool { self.n == 0 }
    #[inline] pub fn sign(&self) -> i32 { if self.n > 0 { 1 } else if self.n < 0 { -1 } else { 0 } }
    #[inline] pub fn neg(self) -> Q { Q { n: -self.n, d: self.d } }
    #[inline] pub fn add(self, o: Q) -> Q {
        if small(&self) && small(&o) { return Q::norm64((self.n as i64) * (o.d as i64) + (o.n as i64) * (self.d as i64), (self.d as i64) * (o.d as i64)); }
        if self.d == 1 && o.d == 1 { return Q { n: addc(self.n, o.n), d: 1 }; }
        if self.d == o.d { return Q::new(addc(self.n, o.n), self.d); }
        let g = gcd(self.d, o.d);
        let (da, db) = (self.d / g, o.d / g);
        Q::new(addc(mulc(self.n, db), mulc(o.n, da)), mulc(self.d, db))
    }
    #[inline] pub fn sub(self, o: Q) -> Q { self.add(o.neg()) }
    #[inline] pub fn mul(self, o: Q) -> Q {
        if self.n == 0 || o.n == 0 { return Q::ZERO; }
        if small(&self) && small(&o) { return Q::norm64((self.n as i64) * (o.n as i64), (self.d as i64) * (o.d as i64)); }
        if self.d == 1 && o.d == 1 { return Q { n: mulc(self.n, o.n), d: 1 }; }
        let g1 = gcd(self.n, o.d); let g2 = gcd(o.n, self.d);
        Q { n: mulc(self.n / g1, o.n / g2), d: mulc(self.d / g2, o.d / g1) }
    }
    #[inline] pub fn inv(self) -> Q { assert!(self.n != 0); if self.n > 0 { Q { n: self.d, d: self.n } } else { Q { n: -self.d, d: -self.n } } }
    #[inline] pub fn div(self, o: Q) -> Q { self.mul(o.inv()) }
    #[inline] pub fn mul_int(self, k: i128) -> Q { self.mul(Q::int(k)) }
    pub fn to_f64(&self) -> f64 { self.n as f64 / self.d as f64 }
    pub fn cmp_q(&self, o: &Q) -> Ordering {
        if self.d == o.d { return self.n.cmp(&o.n); }
        if small(self) && small(o) { return ((self.n as i64) * (o.d as i64)).cmp(&((o.n as i64) * (self.d as i64))); }
        let (sa, sb) = (self.sign(), o.sign());
        if sa != sb { return sa.cmp(&sb); }
        // same sign: compare n1*d2 with n2*d1 (use checked mul; fall back to f64 only on overflow)
        match (self.n.checked_mul(o.d), o.n.checked_mul(self.d)) { (Some(x), Some(y)) => x.cmp(&y), _ => panic!("Q overflow in cmp") }
    }
    /// parse "a", "-a", "a/b"
    pub fn parse(s: &str) -> Q {
        match s.split_once('/') {
            Some((a, b)) => Q::new(a.parse().unwrap_or_else(|_| panic!("bad rational {}", s)), b.parse().unwrap_or_else(|_| panic!("bad rational {}", s))),
            None => Q::int(s.parse().unwrap_or_else(|_| panic!("bad rational {}", s))),
        }
    }
}
impl PartialOrd for Q { fn partial_cmp(&self, o: &Q) -> Option<Ordering> { Some(self.cmp_q(o)) } }
impl Ord for Q { fn cmp(&self, o: &Q) -> Ordering { self.cmp_q(o) } }
impl std::fmt::Display for Q { fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result { if self.d == 1 { write!(f, "{}", self.n) } else { write!(f, "{}/{}", self.n, self.d) } } }

/// exact square root of a rational, if it is a perfect square
pub fn isqrt_u(n: u128) -> u128 {
    if n < 2 { return n; }
    let mut x = (n as f64).sqrt() as u128;
    while x * x > n { x -= 1; }
    while (x + 1) * (x + 1) <= n { x += 1; }
    x
}
pub fn q_sqrt(q: Q) -> Option<Q> {
    if q.n < 0 { return None; }
    let (a, b) = (isqrt_u(q.n as u128), isqrt_u(q.d as u128));
    if a * a == q.n as u128 && b * b == q.d as u128 { Some(Q::new(a as i128, b as i128)) } else { None }
}
/// squarefree part: n = f^2 * d with d squarefree (trial division; n up to ~1e12 in practice)
pub fn squarefree_split(n: u128) -> (u128, u128) {
    let (mut f, mut d, mut m) = (1u128, 1u128, n);
    let mut p = 2u128;
    while p * p <= m {
        let mut e = 0;
        while m % p == 0 { m /= p; e += 1; }
        for _ in 0..e / 2 { f *= p; }
        if e % 2 == 1 { d *= p; }
        p += if p == 2 { 1 } else { 2 };
    }
    d *= m; // leftover prime (or 1)
    (f, d)
}

/// Point (x, y*sqrt(D)).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Pt { pub x: Q, pub y: Q }
impl Pt {
    pub fn new(x: Q, y: Q) -> Pt { Pt { x, y } }
    pub fn sub(self, o: Pt) -> Pt { Pt { x: self.x.sub(o.x), y: self.y.sub(o.y) } }
    pub fn add(self, o: Pt) -> Pt { Pt { x: self.x.add(o.x), y: self.y.add(o.y) } }
    pub fn fx(&self) -> f64 { self.x.to_f64() }
    pub fn fy(&self, sd: f64) -> f64 { self.y.to_f64() * sd }
}
/// sign of the orientation determinant (the common factor sqrt(D) > 0 is dropped)
#[inline] pub fn orient(a: &Pt, b: &Pt, c: &Pt) -> Q {
    b.x.sub(a.x).mul(c.y.sub(a.y)).sub(b.y.sub(a.y).mul(c.x.sub(a.x)))
}
#[inline] pub fn orient_sign(a: &Pt, b: &Pt, c: &Pt) -> i32 { orient(a, b, c).sign() }
/// squared distance, D = squarefree part
#[inline] pub fn dist2(a: &Pt, b: &Pt, dd: i128) -> Q { let dx = a.x.sub(b.x); let dy = a.y.sub(b.y); dx.mul(dx).add(dy.mul(dy).mul_int(dd)) }

/// Unit direction (c, s*sqrt(D)) with c^2 + D s^2 = 1.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct Dir { pub c: Q, pub s: Q }
impl Dir {
    pub fn neg(self) -> Dir { Dir { c: self.c.neg(), s: self.s.neg() } }
    /// complex product
    pub fn rot(self, o: Dir, dd: i128) -> Dir { Dir { c: self.c.mul(o.c).sub(self.s.mul(o.s).mul_int(dd)), s: self.c.mul(o.s).add(self.s.mul(o.c)) } }
    /// upper half-plane class: 0 for angle in [0,pi), 1 for [pi,2pi)
    pub fn half(&self) -> u8 { if self.s.sign() > 0 || (self.s.sign() == 0 && self.c.sign() > 0) { 0 } else { 1 } }
    /// sign of cross(self, o) (>0: o is counter-clockwise of self within pi)
    pub fn cross_sign(&self, o: &Dir) -> i32 { self.c.mul(o.s).sub(self.s.mul(o.c)).sign() }
    pub fn angle_f64(&self, sd: f64) -> f64 { let a = (self.s.to_f64() * sd).atan2(self.c.to_f64()); if a < 0.0 { a + 2.0 * std::f64::consts::PI } else { a } }
}
/// total order of directions by angle in [0, 2pi)
pub fn dir_cmp(a: &Dir, b: &Dir) -> Ordering {
    let (ha, hb) = (a.half(), b.half());
    if ha != hb { return ha.cmp(&hb); }
    if a == b { return Ordering::Equal; }
    match a.cross_sign(b) { 1 => Ordering::Less, -1 => Ordering::Greater, _ => Ordering::Equal }
}
/// unit direction of the vector w = (X, Y sqrt D) whose length is the rational `len`
pub fn dir_of(w: &Pt, len: Q) -> Dir { Dir { c: w.x.div(len), s: w.y.div(len) } }
