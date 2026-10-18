//! M4c: macro layer.  Corner-fill over a vocabulary of convex PIECES, each an exact union of tiles:
//!   tri(s)        : the tile scaled by s (s^2 tiles), 6 placements (3 corners x 2 chiralities) per scale;
//!   brick(x,y,m,n): parallelogram with sides m*x, n*y (x, y two tile sides) and the tile angle between x and y (or its supplement),
//!                   2*m*n tiles, 4 placements (2 corner angles x 2 first-edge choices);  strips = bricks with n = 1.
//! (trapezoids tri(s)\tri(s') are NOT built.)  Same branching rule as the tile layer: at a free corner v with first free ray d
//! exactly one piece has a corner at v with an edge along d, and the corner angle theta <= the free arc.  Exact arithmetic (field.rs),
//! no floats except bounding boxes.  Pruning: dead arc (free arc not x*alpha+y*beta+z*gamma), any corner without a fitting piece.
//! NO_TILING from this layer would only mean "no tiling by these pieces": it is a FINDER, never a refuter.  A FOUND macro tiling is
//! expanded to the explicit tile list and re-verified by the exact verifier (verify.rs).  No nogoods / CBJ here; MRV over corners.
use crate::field::*;
use crate::geom::*;
use crate::verify;
use crate::search::{Mk, tbit, MBITS};
use std::collections::{HashMap, HashSet};
use std::time::Instant;

fn luby(i: u64) -> u64 { let mut i = i; loop { let mut k = 1u64; while (1u64 << k) - 1 < i { k += 1; } if (1u64 << k) - 1 == i { return 1u64 << (k - 1); } i -= (1u64 << (k - 1)) - 1; } }
fn rotp(d: &Dir, p: &Pt, dd: i128) -> Pt { Pt::new(d.c.mul(p.x).sub(d.s.mul(p.y).mul_int(dd)), d.c.mul(p.y).add(d.s.mul(p.x))) }
fn unit_of(w: &Pt, dd: i128) -> Dir { let len = q_sqrt(dist2(w, &Pt::new(Q::ZERO, Q::ZERO), dd)).unwrap_or_else(|| panic!("irrational edge")); dir_of(w, len) }
fn bb_of(pts: &[Pt], sd: f64) -> [f64; 4] {
    let mut b = [f64::MAX, f64::MAX, f64::MIN, f64::MIN];
    for p in pts { let (x, y) = (p.fx(), p.fy(sd)); b[0] = b[0].min(x); b[1] = b[1].min(y); b[2] = b[2].max(x); b[3] = b[3].max(y); }
    b
}
const MARG: f64 = 1e-6;
fn bb_over(a: &[f64; 4], b: &[f64; 4]) -> bool { a[0] <= b[2] + MARG && b[0] <= a[2] + MARG && a[1] <= b[3] + MARG && b[1] <= a[3] + MARG }
/// interior-disjoint test for convex ccw polygons: a separating edge line of one of them
fn disjoint(a: &[Pt], b: &[Pt]) -> bool {
    for (p, q) in [(a, b), (b, a)] {
        let k = p.len();
        for i in 0..k { if q.iter().all(|x| orient_sign(&p[i], &p[(i + 1) % k], x) <= 0) { return true; } }
    }
    false
}

#[derive(Clone)]
pub struct Proto { pub name: String, pub pts: Vec<Pt>, pub ed: Vec<Dir>, pub theta: Dir, pub cnt: i64, pub tiles: Vec<[Pt; 3]> }

fn mk_proto(name: String, pts: Vec<Pt>, theta: Dir, cnt: i64, tiles: Vec<[Pt; 3]>, dd: i128) -> Proto {
    let k = pts.len();
    let ed: Vec<Dir> = (0..k).map(|i| unit_of(&pts[(i + 1) % k].sub(pts[i]), dd)).collect();
    Proto { name, pts, ed, theta, cnt, tiles }
}

pub fn build_vocab(spec: &Spec, smax: i128, bmax: i128) -> Vec<Proto> {
    let dd = spec.dd; let z = Q::ZERO;
    let mut v: Vec<Proto> = Vec::new(); let mut seen: HashSet<Vec<Pt>> = HashSet::new();
    for s in 1..=smax {
        for (si, sl) in spec.slots.iter().enumerate() {
            let (l1, l2) = (Q::int(sl.l1 * s), Q::int(sl.l2 * s));
            let p0 = Pt::new(z, z); let p1 = Pt::new(l1, z); let p2 = Pt::new(l2.mul(sl.psi.c), l2.mul(sl.psi.s));
            if !seen.insert(vec![p0, p1, p2]) { continue; }
            let lat = |i: i128, j: i128| -> Pt { Pt::new(p1.x.mul(Q::new(i, s)).add(p2.x.mul(Q::new(j, s))), p1.y.mul(Q::new(i, s)).add(p2.y.mul(Q::new(j, s)))) };
            let mut tiles = Vec::new();
            for i in 0..s { for j in 0..(s - i) {
                tiles.push([lat(i, j), lat(i + 1, j), lat(i, j + 1)]);
                if i + j + 2 <= s { tiles.push([lat(i + 1, j), lat(i + 1, j + 1), lat(i, j + 1)]); }
            } }
            v.push(mk_proto(format!("tri{}_{}", s, si), vec![p0, p1, p2], sl.psi, (s * s) as i64, tiles, dd));
        }
    }
    let sides = spec.sides;
    for &(i, j) in &[(0usize, 1usize), (1, 2), (0, 2)] {
        let k = 3 - i - j; let phi = spec.ang[k]; let (x, y) = (sides[i], sides[j]);
        for m in 1..=bmax { for n in 1..=bmax { for which in 0..2 { for swap in 0..2 {
            let theta = if which == 0 { phi } else { Dir { c: phi.c.neg(), s: phi.s } };
            let (l1, c1, l2, c2) = if swap == 0 { (m * x, m, n * y, n) } else { (n * y, n, m * x, m) };
            let q0 = Pt::new(z, z); let q1 = Pt::new(Q::int(l1), z); let q3 = Pt::new(Q::int(l2).mul(theta.c), Q::int(l2).mul(theta.s)); let q2 = q1.add(q3);
            if !seen.insert(vec![q0, q1, q2, q3]) { continue; }
            let u = Pt::new(q1.x.div(Q::int(c1)), q1.y.div(Q::int(c1))); let w = Pt::new(q3.x.div(Q::int(c2)), q3.y.div(Q::int(c2)));
            let mut tiles = Vec::new();
            for a in 0..c1 { for b in 0..c2 {
                let o = Pt::new(u.x.mul(Q::int(a)).add(w.x.mul(Q::int(b))), u.y.mul(Q::int(a)).add(w.y.mul(Q::int(b))));
                let (c0, c1p, c2p, c3) = (o, o.add(u), o.add(u).add(w), o.add(w));
                if theta == phi { tiles.push([c0, c1p, c3]); tiles.push([c2p, c1p, c3]); } else { tiles.push([c1p, c2p, c0]); tiles.push([c3, c0, c2p]); }
            } }
            v.push(mk_proto(format!("brick{}x{}_{}x{}_{}{}", l1, l2, c1, c2, which, swap), vec![q0, q1, q2, q3], theta, (2 * m * n) as i64, tiles, dd));
        } } } }
    }
    v.sort_by(|a, b| b.cnt.cmp(&a.cnt));
    v
}

struct Pc { pts: Vec<Pt>, ed: Vec<Dir>, bb: [f64; 4], proto: usize, v: Pt, d: Dir }
enum Loc { Out, Interior, Vertex(usize), Edge(usize) }
fn locate(pts: &[Pt], v: &Pt) -> Loc {
    let k = pts.len(); let mut zero = None;
    for i in 0..k { let o = orient_sign(&pts[i], &pts[(i + 1) % k], v); if o < 0 { return Loc::Out; } if o == 0 { zero = Some(i); } }
    if let Some(i) = (0..k).find(|&i| pts[i] == *v) { return Loc::Vertex(i); }
    match zero { None => Loc::Interior, Some(i) => Loc::Edge(i) }
}

pub struct Ms<'a> {
    inst: &'a Instance, pub vocab: Vec<Proto>, placed: Vec<Pc>, remaining: i64, pub nodes: u64, pub cap: u64, deadline: Option<Instant>, rep: Option<HashSet<Dir>>,
    pub aborted: bool, pub maxdepth: usize, pub dead_prunes: u64,
    pub nogoods_on: bool, pub found: bool, kid: HashMap<(usize, Pt, Dir), u32>, keys: Vec<u32>, kset: HashMap<u32, usize>, nogoods: Vec<Vec<u32>>, ngidx: HashMap<u32, Vec<usize>>, ngseen: HashSet<Vec<u32>>, pub ng_hits: u64, pub ngcap: usize, pub jumps: u64,
    pub cornermacro: bool, pub lex: bool, pub porder: u8, rng: u64, node_cap_seg: u64, pub restarts: u64, pub total_nodes: u64,
}
impl<'a> Ms<'a> {
    pub fn new(inst: &'a Instance, smax: i128, bmax: i128, vt: bool, cap: u64, tl: f64) -> Ms<'a> {
        let vocab = build_vocab(&inst.spec, smax, bmax);
        let rep = if vt { Self::angle_table(&inst.spec) } else { None };
        Ms { inst, vocab, placed: Vec::new(), remaining: inst.n as i64, nodes: 0, cap, deadline: if tl > 0.0 { Some(Instant::now() + std::time::Duration::from_secs_f64(tl)) } else { None }, rep, aborted: false, maxdepth: 0, dead_prunes: 0, nogoods_on: true, found: false, kid: HashMap::new(), keys: Vec::new(), kset: HashMap::new(), nogoods: Vec::new(), ngidx: HashMap::new(), ngseen: HashSet::new(), ng_hits: 0, ngcap: 2_000_000, jumps: 0,
            cornermacro: false, lex: false, porder: 0, rng: 0x9E3779B97F4A7C15, node_cap_seg: u64::MAX, restarts: 0, total_nodes: 0 }
    }
    /// all x*alpha + y*beta + z*gamma (non-negative integers, not all 0) with angle < pi (+slack, a superset is safe); None if too many
    fn angle_table(spec: &Spec) -> Option<HashSet<Dir>> {
        let dd = spec.dd; let ang: Vec<Dir> = spec.ang.to_vec(); let fa: Vec<f64> = ang.iter().map(|a| a.angle_f64(spec.sd)).collect();
        let pi = std::f64::consts::PI + 1e-9;
        let bnd: Vec<i64> = fa.iter().map(|a| (pi / a).floor() as i64).collect();
        if (bnd[0] + 1) * (bnd[1] + 1) * (bnd[2] + 1) > 3_000_000 { return None; }
        let mut set = HashSet::new();
        let one = Dir { c: Q::ONE, s: Q::ZERO };
        let mut dx = one;
        for x in 0..=bnd[0] {
            let mut dy = dx;
            for y in 0..=bnd[1] {
                let mut dz = dy;
                for z in 0..=bnd[2] {
                    if x + y + z > 0 && x as f64 * fa[0] + y as f64 * fa[1] + z as f64 * fa[2] < pi { set.insert(dz); }
                    dz = dz.rot(ang[2], dd);
                }
                dy = dy.rot(ang[1], dd);
            }
            dx = dx.rot(ang[0], dd);
        }
        Some(set)
    }
    fn cut(&mut self) -> bool {
        if self.nodes >= self.cap || self.nodes >= self.node_cap_seg { self.aborted = true; }
        if self.nodes & 63 == 0 { if let Some(d) = self.deadline { if Instant::now() >= d { self.aborted = true; } } }
        self.aborted
    }
    /// admissible free arcs at v: (d, dend, arc angle as a Dir)
    fn arcs_at(&self, v: Pt) -> (Vec<(Dir, Dir)>, Mk) {
        let tgt = &self.inst.target; let sd = self.inst.spec.sd;
        let mut res = Vec::new(); let mut cm = Mk::ZERO;
        if !tgt.contains(&v) { return (res, cm); }
        let mut iv: Vec<(Dir, Dir, bool)> = Vec::with_capacity(12);
        for i in 0..3 { if orient_sign(&tgt.v[i], &tgt.v[(i + 1) % 3], &v) == 0 { iv.push((tgt.dir[i].neg(), tgt.dir[i], true)); } }
        let vb = [v.fx(), v.fy(sd), v.fx(), v.fy(sd)];
        for (pidx, p) in self.placed.iter().enumerate() {
            if !bb_over(&p.bb, &vb) { continue; }
            match locate(&p.pts, &v) {
                Loc::Out => {}
                Loc::Interior => return (Vec::new(), cm),
                Loc::Vertex(k) => { cm |= tbit(pidx); let kk = p.pts.len(); iv.push((p.ed[k], p.ed[(k + kk - 1) % kk].neg(), false)); }
                Loc::Edge(i) => { cm |= tbit(pidx); iv.push((p.ed[i], p.ed[i].neg(), true)); }
            }
        }
        if iv.is_empty() { return (res, cm); }
        let mut u: Vec<Dir> = Vec::with_capacity(2 * iv.len());
        for &(s, e, _) in &iv { u.push(s); u.push(e); }
        u.sort_by(dir_cmp); u.dedup();
        let k = u.len();
        let contained = |x: &Dir| -> bool { iv.iter().any(|&(s, e, hp)| { if *x == s { return true; } if hp { s.cross_sign(x) > 0 } else { s.cross_sign(x) > 0 && x.cross_sign(&e) > 0 } }) };
        let free: Vec<bool> = (0..k).map(|i| !contained(&u[i])).collect();
        if free.iter().all(|&f| f) { return (res, cm); }
        let start = (0..k).find(|&i| !free[i]).unwrap();
        let mut arcs: Vec<(Dir, Dir)> = Vec::new();
        let mut i = 0;
        while i < k {
            let idx = (start + i) % k;
            if free[idx] {
                let ds = u[idx]; let mut j = i; let mut last = idx;
                while j < k && free[(start + j) % k] { last = (start + j) % k; j += 1; }
                arcs.push((ds, u[(last + 1) % k]));
                i = j;
            } else { i += 1; }
        }
        let na = arcs.len();
        for ai in 0..na {
            let (d, dend) = arcs[ai]; let prev_end = arcs[(ai + na - 1) % na].1;
            if d.cross_sign(&prev_end) <= 0 { continue; }
            res.push((d, dend));
        }
        (res, cm)
    }
    fn make(&self, pi: usize, v: Pt, d: Dir) -> Pc {
        let dd = self.inst.spec.dd; let pr = &self.vocab[pi];
        let pts: Vec<Pt> = pr.pts.iter().map(|p| rotp(&d, p, dd).add(v)).collect();
        let ed: Vec<Dir> = pr.ed.iter().map(|e| e.rot(d, dd)).collect();
        let bb = bb_of(&pts, self.inst.spec.sd);
        Pc { pts, ed, bb, proto: pi, v, d }
    }
    /// feasible placements at (v,d,dend) + the conflict mask (blockers of angle-fitting, in-target candidates that overlap a placed piece)
    fn candidates(&self, v: Pt, d: Dir, dend: Dir, cm: Mk) -> (Vec<Pc>, Mk) {
        let dd = self.inst.spec.dd; let mut out = Vec::new(); let mut mask = cm;
        let at_corner = self.inst.target.v.contains(&v);
        for (pi, pr) in self.vocab.iter().enumerate() {
            if self.cornermacro && pr.cnt > 1 && !at_corner { continue; }
            let e2 = d.rot(pr.theta, dd);
            let fits = e2 == dend || (d.cross_sign(&e2) > 0 && e2.cross_sign(&dend) > 0);
            if !fits { continue; }
            let pc = self.make(pi, v, d);
            if !pc.pts.iter().all(|p| self.inst.target.contains(p)) { continue; }
            let mut hit: Option<usize> = None; let mut covered = false;
            for (qi, q) in self.placed.iter().enumerate() {
                if bb_over(&q.bb, &pc.bb) && !disjoint(&q.pts, &pc.pts) { if mask.has(qi) { covered = true; break; } if hit.is_none() { hit = Some(qi); } }
            }
            if covered { continue; }
            match hit { Some(qi) => { mask |= tbit(qi); } None => out.push(pc) }
        }
        (out, mask)
    }
    fn rnd(&mut self) -> u64 { self.rng ^= self.rng << 13; self.rng ^= self.rng >> 7; self.rng ^= self.rng << 17; self.rng }
    fn dead_arc(&self, d: &Dir, dend: &Dir) -> bool {
        match &self.rep { None => false, Some(set) => { let a = dend.rot(Dir { c: d.c, s: d.s.neg() }, self.inst.spec.dd); !set.contains(&a) } }
    }
    fn key_of(&mut self, pc: &Pc) -> u32 {
        let k = (pc.proto, pc.v, pc.d);
        if let Some(&i) = self.kid.get(&k) { return i; }
        let i = self.kid.len() as u32; self.kid.insert(k, i); i
    }
    fn lookup(&self) -> Option<Mk> {
        if !self.nogoods_on { return None; }
        let k = *self.keys.last()?;
        if let Some(ids) = self.ngidx.get(&k) {
            for &id in ids {
                let mut m = Mk::ZERO; let mut ok = true;
                for kk in &self.nogoods[id] { match self.kset.get(kk) { Some(&i) => m |= tbit(i), None => { ok = false; break; } } }
                if ok { return Some(m); }
            }
        }
        None
    }
    fn record(&mut self, m: Mk) {
        if !self.nogoods_on || self.nogoods.len() >= self.ngcap { return; }
        let mut ks: Vec<u32> = (0..self.placed.len()).filter(|&i| m.has(i)).map(|i| self.keys[i]).collect();
        if ks.is_empty() { return; }
        ks.sort();
        if self.ngseen.contains(&ks) { return; }
        let id = self.nogoods.len();
        for k in &ks { self.ngidx.entry(*k).or_default().push(id); }
        self.ngseen.insert(ks.clone()); self.nogoods.push(ks);
    }
    pub fn search(&mut self) -> bool { self.found = false; self.solve(); self.found }
    /// None = found or aborted; Some(mask) = this node fails, `mask` = placed pieces that explain it (conflict-directed backjumping)
    fn solve(&mut self) -> Option<Mk> {
        self.nodes += 1;
        if self.cut() { return None; }
        if self.placed.len() > self.maxdepth { self.maxdepth = self.placed.len(); }
        if self.remaining == 0 { self.found = true; return None; }
        if self.placed.len() >= MBITS - 1 { self.aborted = true; return None; }
        if let Some(m) = self.lookup() { self.ng_hits += 1; return Some(m); }
        let mut pts: Vec<Pt> = self.inst.target.v.to_vec();
        for p in &self.placed { for x in &p.pts { if !pts.contains(x) { pts.push(*x); } } }
        // (rank key, vertex, candidates, arc mask)
        let mut best: Option<((usize, (Q, Q)), Vec<Pc>, Mk)> = None;
        let mut lexbest: Option<((Q, Q), usize)> = None; let mut all: Vec<((Q, Q), Vec<Pc>, Mk)> = Vec::new();
        for v in pts {
            let (arcs, cm) = self.arcs_at(v);
            for (d, dend) in arcs {
                if self.dead_arc(&d, &dend) { self.dead_prunes += 1; return Some(cm); }
                let (c, mask) = self.candidates(v, d, dend, cm);
                if c.is_empty() { return Some(mask); }
                let vk = (v.y, v.x);
                if self.lex {
                    if lexbest.map_or(true, |b| vk < b.0) { lexbest = Some((vk, all.len())); }
                    all.push((vk, c, mask));
                } else {
                    let key = (c.len(), vk);
                    if best.as_ref().map_or(true, |b| key < b.0) { best = Some((key, c, mask)); }
                }
            }
        }
        let (mut cands, amask) = if self.lex {
            match lexbest { Some((_, i)) => { let t = all.swap_remove(i); (t.1, t.2) } None => return Some(Mk::ZERO) }
        } else { match best { Some(b) => (b.1, b.2), None => return Some(Mk::ZERO) } };
        match self.porder {
            1 => cands.sort_by_key(|c| self.vocab[c.proto].cnt),
            2 => { for i in (1..cands.len()).rev() { let j = (self.rnd() % (i as u64 + 1)) as usize; cands.swap(i, j); } }
            3 => { for i in (1..cands.len()).rev() { let j = (self.rnd() % (i as u64 + 1)) as usize; cands.swap(i, j); } cands.sort_by_key(|c| std::cmp::Reverse(self.vocab[c.proto].cnt)); }
            _ => {}
        }
        let depth = self.placed.len(); let bit = tbit(depth); let clr = !bit;
        let mut m = amask;
        for pc in cands {
            let cnt = self.vocab[pc.proto].cnt;
            let k = self.key_of(&pc);
            self.remaining -= cnt; self.keys.push(k); self.kset.insert(k, depth); self.placed.push(pc);
            let r = self.solve();
            if self.found { return None; }
            self.placed.pop(); self.kset.remove(&k); self.keys.pop(); self.remaining += cnt;
            match r {
                None => return None,
                Some(mm) => {
                    if self.nogoods_on && (mm & bit).is_zero() { self.jumps += 1; return Some(mm); }
                    m |= mm & clr;
                }
            }
        }
        self.record(m);
        Some(m)
    }
    pub fn expand(&self) -> Vec<[Pt; 3]> {
        let dd = self.inst.spec.dd; let mut out = Vec::new();
        for p in &self.placed { for t in &self.vocab[p.proto].tiles { out.push([rotp(&p.d, &t[0], dd).add(p.v), rotp(&p.d, &t[1], dd).add(p.v), rotp(&p.d, &t[2], dd).add(p.v)]); } }
        out
    }
    pub fn census(&self) -> String {
        let mut m: HashMap<String, usize> = HashMap::new();
        for p in &self.placed { let n = &self.vocab[p.proto].name; let key = if n.starts_with("tri") { format!("tri{}", n[3..].split('_').next().unwrap()) } else { "brick".to_string() }; *m.entry(key).or_default() += 1; }
        let mut v: Vec<_> = m.into_iter().collect(); v.sort();
        v.iter().map(|(k, c)| format!("{}x{}", k, c)).collect::<Vec<_>>().join(",")
    }
    /// Luby restarts, each with a node cap unit*luby(i); randomized piece order (porder 2/3)
    pub fn run_restarts(&mut self, unit: u64) -> bool {
        let mut i = 1u64; self.total_nodes = 0;
        loop {
            self.nodes = 0; self.aborted = false; self.node_cap_seg = unit * luby(i); self.placed.clear(); self.kset.clear(); self.keys.clear(); self.remaining = self.inst.n as i64;
            let r = self.search();
            self.total_nodes += self.nodes;
            if r { self.nodes = self.total_nodes; return true; }
            if !self.aborted { self.nodes = self.total_nodes; return false; } // vocabulary exhausted (complete search of the macro space)
            if self.deadline_hit() || self.total_nodes >= self.cap { self.nodes = self.total_nodes; return false; }
            i += 1; self.restarts += 1;
        }
    }
    pub fn npieces(&self) -> usize { self.placed.len() }
}

pub fn cli(inst: &Instance, opts: &HashMap<String, String>, _flags: &[String], path: &str) {
    let g = |k: &str| opts.get(k).cloned();
    let smax: i128 = g("S").map_or(1, |x| x.parse().unwrap()); let bmax: i128 = g("B").map_or(0, |x| x.parse().unwrap());
    let cap: u64 = g("cap").map_or(u64::MAX, |x| x.parse().unwrap()); let tl: f64 = g("tl").map_or(0.0, |x| x.parse().unwrap());
    let vt = g("vt").map_or(true, |x| x != "0");
    let t0 = Instant::now();
    let mut m = Ms::new(inst, smax, bmax, vt, cap, tl);
    let nv = m.vocab.len();
    m.lex = g("order").map_or(false, |x| x == "lex"); m.porder = g("porder").map_or(0, |x| x.parse().unwrap());
    let unit: u64 = g("restart").map_or(0, |x| x.parse().unwrap()); m.rng = g("seed").map_or(1u64, |x| x.parse().unwrap()).wrapping_mul(0x9E3779B97F4A7C15) | 1;
    m.cornermacro = g("cornermacro").map_or(false, |x| x == "1");
    m.nogoods_on = g("ng").map_or(true, |x| x != "0");
    let found = if unit == 0 { m.search() } else { m.run_restarts(unit) };
    let secs = t0.elapsed().as_secs_f64();
    let sd = &inst.spec.sides; let tlen = &inst.target.len;
    let mut extra = String::new();
    let verdict = if found { "FOUND" } else if m.aborted { if m.deadline_hit() { "TIMEOUT" } else { "CAPPED" } } else { "EXHAUSTED_VOCAB" };
    if found {
        let tiles = m.expand();
        let out = g("tiling").unwrap_or_else(|| format!("{}.macro.found.txt", path));
        crate::write_tiling(inst, &inst.target.v, &tiles, &out);
        let mut tl2 = verify::load(&out); let rep = verify::verify(&mut tl2);
        extra = format!(" pieces=[{}] tiles_expanded={} tiling={} exact_verify={}", m.census(), tiles.len(), out, if rep.ok() { "VERIFIED" } else { "FAILED" });
    }
    println!("bte-macro ({},{},{}) in ({},{},{}) N={} S={} B={} vt={} vocab={} cornermacro={} order={} porder={} restarts={} ng={} nogoods={} hits={} jumps={} nodes={} maxdepth={} dead_prunes={} verdict={} secs={:.1}{}{}",
        sd[0], sd[1], sd[2], tlen[0], tlen[1], tlen[2], inst.n, smax, bmax, vt as u8, nv, m.cornermacro as u8, if m.lex { "lex" } else { "mrv" }, m.porder, m.restarts, m.nogoods_on as u8, m.nogoods.len(), m.ng_hits, m.jumps, m.nodes, m.maxdepth, m.dead_prunes, verdict, secs, extra,
        if verdict == "EXHAUSTED_VOCAB" { " (NOT a refutation: no tiling by these pieces only)" } else { "" });
}
impl<'a> Ms<'a> { fn deadline_hit(&self) -> bool { self.deadline.map_or(false, |d| Instant::now() >= d) } }
