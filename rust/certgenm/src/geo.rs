//! Port of lean/gen_tree.py: exact geometry over Q(sqrt Dn) in rescaled coordinates, the angular
//! machinery (build23.py), and the refutation-tree construction.  Points are (X, Y) = (X, Y*sqrt(Dn)).
use crate::rat::Q;
use std::cmp::Ordering;

pub type P = (Q, Q);
pub type Tri = [P; 3];

pub fn q(x: i64) -> Q {
    Q::int(x)
}

pub struct Geo {
    pub dn: Q,
    pub t: Vec<P>, // CCW, (0,0),(tx,0),(ax,ay)
    pub sides: [Q; 3],
}

impl Geo {
    pub fn new(dn: Q, t: Vec<P>, sides: [Q; 3]) -> Geo {
        Geo { dn, t, sides }
    }
    pub fn sub(&self, a: &P, b: &P) -> P {
        (&a.0 - &b.0, &a.1 - &b.1)
    }
    pub fn add(&self, a: &P, b: &P) -> P {
        (&a.0 + &b.0, &a.1 + &b.1)
    }
    pub fn smul(&self, s: &Q, a: &P) -> P {
        (s * &a.0, s * &a.1)
    }
    pub fn cross(&self, u: &P, v: &P) -> Q {
        &u.0 * &v.1 - &u.1 * &v.0
    }
    pub fn dot(&self, u: &P, v: &P) -> Q {
        &u.0 * &v.0 + &self.dn * &u.1 * &v.1
    }
    pub fn norm2(&self, u: &P) -> Q {
        self.dot(u, u)
    }
    pub fn ef(&self, a: &P, b: &P, p: &P) -> Q {
        (&b.0 - &a.0) * (&p.1 - &a.1) - (&p.0 - &a.0) * (&b.1 - &a.1)
    }
    pub fn inside(&self, tri: &[P], p: &P, strict: bool) -> bool {
        let n = tri.len();
        for i in 0..n {
            let e = self.ef(&tri[i], &tri[(i + 1) % n], p);
            if e.is_neg() || (strict && e.is_zero()) {
                return false;
            }
        }
        true
    }
    pub fn perp(&self, d: &P) -> P {
        (-(&self.dn * &d.1), d.0.clone())
    }
    pub fn unit(&self, w: &P) -> Option<P> {
        let l = self.norm2(w).sqrt_exact()?;
        if l.is_zero() {
            return None;
        }
        Some((&w.0 / &l, &w.1 / &l))
    }
    fn clip(&self, poly: &[P], a: &P, b: &P) -> Vec<P> {
        let mut out = Vec::new();
        let n = poly.len();
        for i in 0..n {
            let (p, qq) = (&poly[i], &poly[(i + 1) % n]);
            let (fp, fq) = (self.ef(a, b, p), self.ef(a, b, qq));
            if !fp.is_neg() {
                out.push(p.clone());
            }
            if (fp.is_neg() && fq.is_pos()) || (fq.is_neg() && fp.is_pos()) {
                let t = &fp / &(&fp - &fq);
                out.push((&p.0 + &t * (&qq.0 - &p.0), &p.1 + &t * (&qq.1 - &p.1)));
            }
        }
        out
    }
    fn intersect(&self, t1: &Tri, t2: &Tri) -> Vec<P> {
        let mut poly: Vec<P> = t1.to_vec();
        for i in 0..3 {
            poly = self.clip(&poly, &t2[i], &t2[(i + 1) % 3]);
            if poly.is_empty() {
                return vec![];
            }
        }
        poly
    }
    fn area2(&self, poly: &[P]) -> Q {
        let mut s = Q::zero();
        for i in 0..poly.len() {
            let (p, qq) = (&poly[i], &poly[(i + 1) % poly.len()]);
            s = s + (&p.0 * &qq.1 - &p.1 * &qq.0);
        }
        s
    }
    fn centroid(&self, poly: &[P]) -> P {
        let n = Q::int(poly.len() as i64);
        let mut sx = Q::zero();
        let mut sy = Q::zero();
        for p in poly {
            sx = sx + &p.0;
            sy = sy + &p.1;
        }
        (sx / &n, sy / &n)
    }
    pub fn overlap_witness(&self, t1: &Tri, t2: &Tri) -> Option<P> {
        let poly = self.intersect(t1, t2);
        if poly.len() < 3 || self.area2(&poly).is_zero() {
            return None;
        }
        let mut uniq: Vec<P> = Vec::new();
        for p in &poly {
            if !uniq.iter().any(|x| x == p) {
                uniq.push(p.clone());
            }
        }
        if uniq.len() < 3 || self.area2(&uniq).is_zero() {
            return None;
        }
        let w = self.centroid(&uniq);
        assert!(self.inside(t1, &w, true) && self.inside(t2, &w, true));
        Some(w)
    }
}

#[derive(Clone, Debug)]
pub enum Kill {
    Escape(usize, usize), // (kidx 2=Q / 1=P, target edge)
    Overlap(usize, P),
}

#[derive(Clone, Debug)]
pub struct Rec {
    pub l: (Q, Q, Q),
    pub p: Q,
    pub q: Q,
    pub tri: Tri,
    pub kill: Option<Kill>,
}

pub struct Node {
    pub tiles: Vec<Tri>,
    pub v: P,
    pub d: P,
    pub recs: Vec<Rec>,
    pub children: [Option<usize>; 6],
}

pub struct Cons<'a> {
    pub g: &'a Geo,
    pub six: [(Q, Q, Q); 6],
}

fn sgn(x: &Q) -> i32 {
    x.signum()
}

impl<'a> Cons<'a> {
    pub fn new(g: &'a Geo) -> Cons<'a> {
        let (a, b, c) = (g.sides[0].clone(), g.sides[1].clone(), g.sides[2].clone());
        let six = [
            (a.clone(), c.clone(), b.clone()),
            (c.clone(), a.clone(), b.clone()),
            (a.clone(), b.clone(), c.clone()),
            (b.clone(), a.clone(), c.clone()),
            (c.clone(), b.clone(), a.clone()),
            (b.clone(), c.clone(), a.clone()),
        ];
        Cons { g, six }
    }
    fn half(&self, d: &P) -> i32 {
        let sy = sgn(&d.1);
        if sy > 0 {
            0
        } else if sy < 0 {
            1
        } else if d.0.is_pos() {
            0
        } else {
            1
        }
    }
    fn ang_lt(&self, d1: &P, d2: &P) -> bool {
        let (h1, h2) = (self.half(d1), self.half(d2));
        if h1 != h2 {
            return h1 < h2;
        }
        self.g.cross(d1, d2).is_pos()
    }
    pub fn ang_eq(&self, d1: &P, d2: &P) -> bool {
        self.g.cross(d1, d2).is_zero() && self.g.dot(d1, d2).is_pos()
    }
    fn ang_cmp(&self, a: &P, b: &P) -> Ordering {
        if self.ang_lt(a, b) {
            Ordering::Less
        } else if self.ang_lt(b, a) {
            Ordering::Greater
        } else {
            Ordering::Equal
        }
    }
    fn in_arc(&self, s: &P, e: &P, x: &P) -> bool {
        if self.ang_eq(s, x) || self.ang_eq(e, x) {
            return true;
        }
        !self.g.cross(s, x).is_neg() && !self.g.cross(x, e).is_neg()
    }
    fn sub_in_arc(&self, s: &P, e: &P, d1: &P, d2: &P) -> bool {
        if !(self.in_arc(s, e, d1) && self.in_arc(s, e, d2)) {
            return false;
        }
        let c = self.g.cross(d1, d2);
        if c.is_pos() {
            return true;
        }
        if c.is_zero() {
            if self.g.dot(d1, d2).is_pos() {
                return true;
            }
            return self.ang_eq(s, d1) && self.ang_eq(e, d2);
        }
        false
    }
    pub fn on_seg_interior(&self, p: &P, a: &P, b: &P) -> bool {
        let g = self.g;
        if !g.cross(&g.sub(b, a), &g.sub(p, a)).is_zero() {
            return false;
        }
        let d = g.sub(b, a);
        let t = g.dot(&g.sub(p, a), &d);
        t.is_pos() && t < g.dot(&d, &d)
    }
    fn blocked_arcs(&self, v: &P, tiles: &[Tri]) -> Option<Vec<(P, P)>> {
        let g = self.g;
        let t = &g.t;
        let mut arcs: Vec<(P, P)> = Vec::new();
        let mut hit = false;
        let nt = t.len();
        for i in 0..nt {
            let (a, b) = (&t[i], &t[(i + 1) % nt]);
            if v == a {
                let c = &t[(i + nt - 1) % nt];
                let (db, dc) = (g.sub(b, a), g.sub(c, a));
                let m1 = Q::int(-1);
                arcs.push((dc, g.smul(&m1, &db)));
                arcs.push((g.smul(&m1, &db), db));
                hit = true;
                break;
            }
            if self.on_seg_interior(v, a, b) {
                arcs.push((g.sub(a, b), g.sub(b, a)));
                hit = true;
                break;
            }
        }
        if !hit && !g.inside(t, v, false) {
            return None;
        }
        for tri in tiles {
            let mut done = false;
            for i in 0..3 {
                if *v == tri[i] {
                    let (p, qq) = (&tri[(i + 1) % 3], &tri[(i + 2) % 3]);
                    let (d1, d2) = (g.sub(p, v), g.sub(qq, v));
                    if g.cross(&d1, &d2).is_pos() {
                        arcs.push((d1, d2));
                    } else {
                        arcs.push((d2, d1));
                    }
                    done = true;
                    break;
                }
            }
            if done {
                continue;
            }
            for i in 0..3 {
                let (a, b) = (&tri[i], &tri[(i + 1) % 3]);
                if self.on_seg_interior(v, a, b) {
                    let c = &tri[(i + 2) % 3];
                    if g.cross(&g.sub(b, a), &g.sub(c, a)).is_pos() {
                        arcs.push((g.sub(b, a), g.sub(a, b)));
                    } else {
                        arcs.push((g.sub(a, b), g.sub(b, a)));
                    }
                    done = true;
                    break;
                }
            }
            if done {
                continue;
            }
            if g.inside(tri, v, true) {
                return None;
            }
        }
        Some(arcs)
    }
    pub fn free_dirs(&self, v: &P, tiles: &[Tri]) -> Option<Vec<(P, P)>> {
        let arcs = self.blocked_arcs(v, tiles)?;
        let mut dd: Vec<P> = Vec::new();
        for (s, e) in &arcs {
            for d in [s, e] {
                if !dd.iter().any(|x| self.ang_eq(d, x)) {
                    dd.push(d.clone());
                }
            }
        }
        if dd.len() < 2 {
            return Some(vec![]);
        }
        dd.sort_by(|a, b| self.ang_cmp(a, b));
        let n = dd.len();
        let mut free = Vec::new();
        for i in 0..n {
            let (d1, d2) = (&dd[i], &dd[(i + 1) % n]);
            if !arcs.iter().any(|(s, e)| self.sub_in_arc(s, e, d1, d2)) {
                free.push((d1.clone(), d2.clone()));
            }
        }
        Some(free)
    }
    pub fn pick_point(&self, tiles: &[Tri]) -> Option<(P, P)> {
        let mut cands: Vec<P> = self.g.t.clone();
        for tri in tiles {
            cands.extend(tri.iter().cloned());
        }
        let mut uniq: Vec<P> = Vec::new();
        for p in cands {
            if !uniq.iter().any(|x| *x == p) {
                uniq.push(p);
            }
        }
        uniq.sort_by(|a, b| (&a.1, &a.0).cmp(&(&b.1, &b.0)));
        for v in &uniq {
            let fd = match self.free_dirs(v, tiles) {
                None => continue,
                Some(f) => f,
            };
            if !fd.is_empty() {
                let mut starts: Vec<P> = fd.into_iter().map(|(s, _)| s).collect();
                starts.sort_by(|a, b| self.ang_cmp(a, b));
                return Some((v.clone(), starts.remove(0)));
            }
        }
        None
    }
    pub fn third(&self, v: &P, d: &P, l1: &Q, l2: &Q, l3: &Q) -> (Q, Q, P) {
        let g = self.g;
        let p = (l1 * l1 + l2 * l2 - l3 * l3) / (Q::int(2) * l1);
        let q2 = (l2 * l2 - &p * &p) / &g.dn;
        let qq = q2.sqrt_exact().expect("third vertex not in Q(sqrt Dn)");
        assert!(qq.is_pos(), "third vertex not in Q(sqrt Dn)");
        let pt = (&v.0 + &p * &d.0 - &g.dn * &qq * &d.1, &v.1 + &p * &d.1 + &qq * &d.0);
        (p, qq, pt)
    }
    pub fn classify(&self, v: &P, d: &P, tiles: &[Tri]) -> Vec<Rec> {
        let g = self.g;
        let mut out = Vec::new();
        for (l1, l2, l3) in self.six.iter() {
            let p_pt = g.add(v, &g.smul(l1, d));
            let (p, qq, q_pt) = self.third(v, d, l1, l2, l3);
            let tri: Tri = [v.clone(), p_pt.clone(), q_pt.clone()];
            assert!(g.cross(&g.sub(&p_pt, v), &g.sub(&q_pt, v)).is_pos());
            let mut rec = Rec { l: (l1.clone(), l2.clone(), l3.clone()), p, q: qq, tri: tri.clone(), kill: None };
            'esc: for (pt, kidx) in [(&q_pt, 2usize), (&p_pt, 1usize)] {
                for e in 0..g.t.len() {
                    if g.ef(&g.t[e], &g.t[(e + 1) % g.t.len()], pt).is_neg() {
                        rec.kill = Some(Kill::Escape(kidx, e));
                        break 'esc;
                    }
                }
            }
            if rec.kill.is_some() {
                out.push(rec);
                continue;
            }
            for (m, u) in tiles.iter().enumerate() {
                if let Some(w) = g.overlap_witness(&tri, u) {
                    rec.kill = Some(Kill::Overlap(m, w));
                    break;
                }
            }
            out.push(rec);
        }
        out
    }
}

/// full refutation tree (every live placement recursed); nodes in pre-order numbering
pub fn build_tree(g: &Geo, cons: &Cons, max_nodes: usize) -> Vec<Node> {
    fn rec(g: &Geo, cons: &Cons, tiles: &mut Vec<Tri>, nodes: &mut Vec<Node>, max_nodes: usize) -> usize {
        let nid = nodes.len();
        assert!(nid <= max_nodes, "cap");
        let (v, d0) = cons.pick_point(tiles).unwrap_or_else(|| panic!("no uncovered point at depth {}", tiles.len()));
        let d = g.unit(&d0).expect("irrational ray");
        let recs = cons.classify(&v, &d, tiles);
        nodes.push(Node { tiles: tiles.clone(), v, d, recs: recs.clone(), children: [None; 6] });
        for (i, r) in recs.iter().enumerate() {
            if r.kill.is_none() {
                tiles.push(r.tri.clone());
                let c = rec(g, cons, tiles, nodes, max_nodes);
                nodes[nid].children[i] = Some(c);
                tiles.pop();
            }
        }
        nid
    }
    let mut nodes = Vec::new();
    rec(g, cons, &mut Vec::new(), &mut nodes, max_nodes);
    nodes
}
