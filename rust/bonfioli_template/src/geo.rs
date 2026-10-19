//! Exact planar geometry for one tile family.  Points are (X, Y*sqrt(D)) as in the exact verifier; a direction is an ANGLE VECTOR
//! [m, n, k] = m*alpha + n*beta + k*(pi/q) (mod 2pi); its unit vector is computed exactly in Q(sqrt(-D)).
use crate::field::*;
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

pub type Ang = [i32; 3];
pub fn aadd(x: Ang, y: Ang) -> Ang { [x[0] + y[0], x[1] + y[1], x[2] + y[2]] }
pub fn asub(x: Ang, y: Ang) -> Ang { [x[0] - y[0], x[1] - y[1], x[2] - y[2]] }

pub struct Fam {
    pub name: String, pub dd: i128, pub sides: [i128; 3],      // tile sides a,b,c (opposite alpha,beta,gamma)
    pub tang: [Ang; 3],                                          // tile angles alpha,beta,gamma as angle vectors
    pub q: i32, pub pivec: Ang,                                  // pi = pivec (default [0,0,q])
    pub units: [Dir; 3],                                         // e^{i alpha}, e^{i beta}, e^{i pi/q}
    pub fval: [f64; 3],                                          // alpha, beta, pi/q in radians
    pub pw: RefCell<HashMap<(usize, i32), Dir>>,
    pub dc: RefCell<HashMap<Ang, Dir>>,
}

impl Fam {
    pub fn pi(&self) -> Ang { self.pivec }
    pub fn two_pi(&self) -> Ang { [2 * self.pivec[0], 2 * self.pivec[1], 2 * self.pivec[2]] }
    pub fn val(&self, a: Ang) -> f64 { a[0] as f64 * self.fval[0] + a[1] as f64 * self.fval[1] + a[2] as f64 * self.fval[2] }
    pub fn dir(&self, a: Ang) -> Dir {
        let mut a = a; if self.q > 0 { a[2] = a[2].rem_euclid(2 * self.q); }
        if let Some(d) = self.dc.borrow().get(&a) { return *d; }
        let d = self.pwr(0, a[0]).rot(self.pwr(1, a[1]), self.dd).rot(self.pwr(2, a[2]), self.dd);
        let d = Dir { c: persist(d.c), s: persist(d.s) };
        self.dc.borrow_mut().insert(a, d); d
    }
    fn pwr(&self, i: usize, e: i32) -> Dir {
        if let Some(d) = self.pw.borrow().get(&(i, e)) { return *d; }
        let base = if e >= 0 { self.units[i] } else { Dir { c: self.units[i].c, s: self.units[i].s.neg() } };
        let mut r = Dir { c: Q::ONE, s: Q::ZERO };
        for _ in 0..e.abs() { r = r.rot(base, self.dd); }
        let r = Dir { c: persist(r.c), s: persist(r.s) };
        self.pw.borrow_mut().insert((i, e), r); r
    }
    pub fn tile_side(&self, x: usize, y: usize) -> Q { let z = 3 - x - y; Q::int(self.sides[z]) }
    /// canonical form of an angle used as a vertex interior angle: value in [0, 2pi); 0 vector when the value is 0
    pub fn norm_val(&self, a: Ang) -> Ang {
        let mut a = a; let tp = self.two_pi();
        let mut v = self.val(a);
        while v >= 2.0 * std::f64::consts::PI - 1e-9 { a = asub(a, tp); v = self.val(a); }
        while v < -1e-9 { a = aadd(a, tp); v = self.val(a); }
        if v.abs() < 1e-9 { a = [0, 0, 0]; }
        a
    }
    /// interior angle at a vertex of a CCW polygon, incoming edge direction din, outgoing dout: pi - turn, turn in (-pi, pi]
    pub fn interior(&self, din: Ang, dout: Ang) -> Ang {
        let tp = self.two_pi(); let pi = self.pi();
        let mut turn = asub(dout, din);
        let mut v = self.val(turn);
        while v > std::f64::consts::PI + 1e-9 { turn = asub(turn, tp); v = self.val(turn); }
        while v <= -std::f64::consts::PI + 1e-9 { turn = aadd(turn, tp); v = self.val(turn); }
        asub(pi, turn)
    }
    /// all angle vectors that are sums of tile angles [+ pi], with value in [0, 2pi]
    pub fn fill_set(&self) -> HashSet<Ang> {
        let mut ok: HashSet<Ang> = HashSet::new(); let mut fr: Vec<Ang> = vec![[0, 0, 0]]; ok.insert([0, 0, 0]);
        let lim = 2.0 * std::f64::consts::PI + 1e-9;
        let mut gens: Vec<Ang> = self.tang.to_vec(); gens.push(self.pi());
        while let Some(x) = fr.pop() {
            for g in &gens {
                let y = aadd(x, *g);
                if self.val(y) <= lim && !ok.contains(&y) { ok.insert(y); fr.push(y); }
            }
        }
        ok
    }
}

/// Build a family from the tile sides (a,b,c) and the angle structure.
///  kind "g2a": gamma = 2 alpha ; "gen": generic scalene ; "iso": gamma = 2pi/3 (alpha+beta = pi/3) ; "equi": all pi/3
pub fn make_fam(kind: &str, a: i128, b: i128, c: i128) -> Fam {
    let d0 = ((a + b + c) * (b + c - a) * (a - b + c) * (a + b - c)) as u128;
    let (f, dd) = squarefree_split(d0);
    let (f, dd) = (f as i128, dd as i128);
    let ua = Dir { c: Q::new(b * b + c * c - a * a, 2 * b * c), s: Q::new(f, 2 * b * c) };
    let ub = Dir { c: Q::new(a * a + c * c - b * b, 2 * a * c), s: Q::new(f, 2 * a * c) };
    let fa = (((b * b + c * c - a * a) as f64) / (2.0 * (b * c) as f64)).acos();
    let fb = (((a * a + c * c - b * b) as f64) / (2.0 * (a * c) as f64)).acos();
    let pi = std::f64::consts::PI;
    let (tang, q, uu, fu): ([Ang; 3], i32, Dir, f64) = match kind {
        "gen" => ([[1, 0, 0], [0, 1, 0], [-1, -1, 1]], 1, Dir { c: Q::int(-1), s: Q::ZERO }, pi),
        "g2a" => ([[1, 0, 0], [-3, 0, 1], [2, 0, 0]], 1, Dir { c: Q::int(-1), s: Q::ZERO }, pi),
        "iso" => { assert!(dd == 3); ([[1, 0, 0], [-1, 0, 1], [0, 0, 2]], 3, Dir { c: Q::new(1, 2), s: Q::new(1, 2) }, pi / 3.0) }
        "s3" => ([[1, 0, 0], [0, 1, 0], [2, 1, 0]], 0, Dir { c: Q::ONE, s: Q::ZERO }, 0.0),
        "equi" => { assert!(dd == 3); ([[0, 0, 1], [0, 0, 1], [0, 0, 1]], 3, Dir { c: Q::new(1, 2), s: Q::new(1, 2) }, pi / 3.0) }
        _ => panic!("family kind"),
    };
    let pivec: Ang = if kind == "s3" { [3, 2, 0] } else { [0, 0, q] };
    let s = aadd(aadd(tang[0], tang[1]), tang[2]);
    assert!(s == pivec, "angle sum {:?} for {}", s, kind);
    if kind == "s3" { assert!((3.0 * fa + 2.0 * fb - pi).abs() < 1e-9, "3alpha+2beta != pi for this tile"); }
    if kind == "g2a" { assert!((fb - (pi - 3.0 * fa)).abs() < 1e-9 && ((2.0 * fa) - (pi - fa - fb)).abs() < 1e-9, "not gamma=2alpha"); }
    Fam { name: format!("{}:{},{},{}", kind, a, b, c), dd, sides: [a, b, c], tang, q, pivec, units: [ua, ub, uu], fval: [fa, fb, fu],
        pw: RefCell::new(HashMap::new()), dc: RefCell::new(HashMap::new()) }
}

impl Fam {
    /// angle vector (nonnegative combination i*alpha + j*beta + k*gamma + p*pi, p in {0,1}) with exact cosine `cv`, value in (0, pi)
    pub fn find_ang(&self, cv: Q) -> Option<Ang> {
        let mut best: Option<(i32, Ang)> = None;
        for i in 0..=12i32 { for j in 0..=12i32 { for k in 0..=12i32 { for p in 0..2i32 {
            if i + j + k + p == 0 { continue; }
            let mut a = [0i32; 3];
            for t in 0..3 { a[t] = i * self.tang[0][t] + j * self.tang[1][t] + k * self.tang[2][t] + p * self.pivec[t]; }
            let v = self.val(a);
            if v <= 1e-9 || v >= std::f64::consts::PI - 1e-9 { continue; }
            let d = self.dir(a);
            if d.c == cv && d.s.sign() > 0 { let sc = i + j + k + p; if best.is_none() || sc < best.unwrap().0 { best = Some((sc, a)); } }
        } } } }
        best.map(|b| b.1)
    }
}
