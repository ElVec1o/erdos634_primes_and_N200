//! Tile layer: exhaustive corner-fill search in exact arithmetic (same branching as rust/mrv2, which is the reference).
//!  * a node = the placed tiles + the list of "branches" (a vertex v and a free arc starting at direction d such that all free arcs
//!    at v lie in a pointed cone starting at d); a branch has up to 6 candidate tiles (the slots), each non-overlapping, inside the target;
//!  * options are maintained INCREMENTALLY (child = parent with the candidates that overlap the new tile removed, plus the points
//!    touched by the new tile recomputed); mrv2 recomputes everything at every node;
//!  * conflict-directed backjumping (CBJ) with 1024-bit conflict masks, semantic nogoods (sets of tile keys), proof trees in the
//!    mrv2/certgenx `.tree` format, Luby restarts + frozen-estimate stall detector with nogood retention, perturbed orders.
use crate::field::*;
use crate::geom::*;
use std::cell::Cell;
use std::collections::{HashMap as StdHashMap, HashSet as StdHashSet};
use std::hash::{BuildHasherDefault, Hasher};
#[derive(Default, Clone, Copy)] pub struct Fx(u64);
const FXK: u64 = 0x517cc1b727220a95;
impl Hasher for Fx {
    fn write(&mut self, bytes: &[u8]) { for b in bytes { self.0 = (self.0.rotate_left(5) ^ *b as u64).wrapping_mul(FXK); } }
    fn write_u8(&mut self, i: u8) { self.0 = (self.0.rotate_left(5) ^ i as u64).wrapping_mul(FXK); }
    fn write_u32(&mut self, i: u32) { self.0 = (self.0.rotate_left(5) ^ i as u64).wrapping_mul(FXK); }
    fn write_u64(&mut self, i: u64) { self.0 = (self.0.rotate_left(5) ^ i).wrapping_mul(FXK); }
    fn write_i64(&mut self, i: i64) { self.write_u64(i as u64) }
    fn write_u128(&mut self, i: u128) { self.write_u64(i as u64); self.write_u64((i >> 64) as u64); }
    fn write_usize(&mut self, i: usize) { self.write_u64(i as u64) }
    fn finish(&self) -> u64 { self.0 }
}
type HashMap<K, V> = StdHashMap<K, V, BuildHasherDefault<Fx>>;
type HashSet<K> = StdHashSet<K, BuildHasherDefault<Fx>>;
use std::rc::Rc;
use std::time::Instant;

pub const MW: usize = 16;
pub const MBITS: usize = MW * 64;
#[derive(Clone, Copy, PartialEq, Eq)]
pub struct Mk(pub [u64; MW]);
impl Mk {
    pub const ZERO: Mk = Mk([0; MW]);
    pub const ONES: Mk = Mk([!0u64; MW]);
    pub fn is_zero(&self) -> bool { self.0.iter().all(|&w| w == 0) }
    pub fn count_ones(&self) -> u32 { self.0.iter().map(|w| w.count_ones()).sum() }
    pub fn top(&self) -> u32 { for k in (0..MW).rev() { if self.0[k] != 0 { return (k as u32) * 64 + 64 - self.0[k].leading_zeros(); } } 0 }
    pub fn below(i: usize) -> Mk { let mut m = [0u64; MW]; for k in 0..MW { let lo = k * 64; if i >= lo + 64 { m[k] = !0; } else if i > lo { m[k] = (1u64 << (i - lo)) - 1; } } Mk(m) }
    pub fn has(&self, i: usize) -> bool { let i = i.min(MBITS - 1); self.0[i / 64] >> (i % 64) & 1 == 1 }
}
impl std::ops::BitOr for Mk { type Output = Mk; fn bitor(self, o: Mk) -> Mk { let mut m = self.0; for k in 0..MW { m[k] |= o.0[k]; } Mk(m) } }
impl std::ops::BitAnd for Mk { type Output = Mk; fn bitand(self, o: Mk) -> Mk { let mut m = self.0; for k in 0..MW { m[k] &= o.0[k]; } Mk(m) } }
impl std::ops::Not for Mk { type Output = Mk; fn not(self) -> Mk { let mut m = self.0; for k in 0..MW { m[k] = !m[k]; } Mk(m) } }
impl std::ops::BitOrAssign for Mk { fn bitor_assign(&mut self, o: Mk) { for k in 0..MW { self.0[k] |= o.0[k]; } } }
pub fn tbit(i: usize) -> Mk { let i = i.min(MBITS - 1); let mut m = [0u64; MW]; m[i / 64] = 1u64 << (i % 64); Mk(m) }

// ---------------------------------------------------------------- proof trees (mrv2 format)
pub struct T { pub v: (f64, f64), pub d: (f64, f64), pub kids: Vec<(usize, Rc<T>)>, pub stub: Option<usize>, pub def: Cell<Option<usize>> }
pub type R = Option<(u64, Mk, Rc<T>)>;
fn mk(v: (f64, f64), d: (f64, f64), kids: Vec<(usize, Rc<T>)>) -> Rc<T> { Rc::new(T { v, d, kids, stub: None, def: Cell::new(None) }) }
fn collect(t: &T, refs: &mut HashSet<usize>, table: &[Rc<T>]) {
    if let Some(id) = t.stub { if refs.insert(id) { collect(&table[id], refs, table); } return; }
    for (_, k) in &t.kids { collect(k, refs, table); }
}
fn emit(t: &T, root: bool, refs: &HashSet<usize>, table: &[Rc<T>], out: &mut String) -> u64 {
    let rid = if let Some(id) = t.stub { Some(id) } else if !root { t.def.get().filter(|id| refs.contains(id)) } else { None };
    if let Some(id) = rid { out.push_str(&format!("S {}\n", id)); return 1; }
    let mut sl = [0u8; 6];
    for (i, _) in &t.kids { sl[*i] = 1; }
    out.push_str(&format!("T {:.12} {:.12} {:.12} {:.12} {} {} {} {} {} {}\n", t.v.0, t.v.1, t.d.0, t.d.1, sl[0], sl[1], sl[2], sl[3], sl[4], sl[5]));
    let mut n = 1;
    for (_, k) in &t.kids { n += emit(k, false, refs, table, out); }
    n
}

// ---------------------------------------------------------------- state
pub type Key = [i64; 6];
#[derive(Clone)]
pub struct Cand { pub slot: u8, pub p: Pt, pub q: Pt, pub bb: [f64; 4] }
/// `cmask` = tiles covering the point; `blocked` = candidate slots eliminated by an overlapping placed tile (sorted by slot).  The conflict set of
/// the branch is rebuilt lazily by `fresh_mask` exactly as rust/mrv2 builds it (per blocked slot: nothing if an overlapping tile is already in the
/// mask, else the lowest-index overlapping tile).
pub struct Opt { pub v: Pt, pub d: Dir, pub dend: Dir, pub phi: f64, pub feas: Vec<Cand>, pub blocked: Vec<Cand>, pub cmask: Mk }
#[derive(Clone)]
pub struct Tile { pub p: [Pt; 3], pub rays: [Dir; 6], pub bb: [f64; 4], pub slot: u8 }

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum Order { Mrv, Lex, Band(f64) }

#[derive(Clone)]
pub struct Cfg {
    pub order: Order, pub la: u32, pub cbj: bool, pub cap: u64, pub w: u64, pub ng: bool, pub ngcap: usize, pub notree: bool,
    pub tl: f64,                 // wall-clock limit (s), 0 = none
    pub restart_unit: u64,       // Luby unit in main calls (0 = no Luby restarts)
    pub stall_ticks: u32,        // frozen-estimate detector: restart after this many consecutive frozen ticks (0 = off)
    pub tick: u64,               // main calls between detector ticks
    pub perturb: bool,           // new order after each restart
    pub pmode: String,           // which perturbations: t = random tie-break, s = shuffled child order, w = random sweep functional
    pub seed: u64,
    pub report_secs: f64,
    pub mirror_slots: Option<Vec<usize>>, // root slot filter (verdict only)
    pub tb0: u64,               // initial random tie-break seed among equal keys (0 = deterministic x order)
    pub sweep: Option<(i64, i64)>, // lex key = w1*x + w2*y (default: y, then x)
    pub wallgap_on: bool,        // target-edge gap rule (verdict only, NOT a certificate)
    pub sym: bool,               // half-triangle symmetry (isosceles target): verdict only, NOT a certificate
    pub selfcheck: bool,         // debug: at every node compare the incremental options with a full recomputation
    pub wallgap: bool,
    pub stop: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>, // portfolio: another worker has a verdict
    pub deadline: Option<Instant>, // portfolio: global wall limit
}
impl Default for Cfg {
    fn default() -> Cfg { Cfg { order: Order::Mrv, la: 0, cbj: true, cap: u64::MAX, w: 1000, ng: true, ngcap: 3_000_000, notree: false, tl: 0.0, restart_unit: 0, stall_ticks: 0, tick: 20000, perturb: true, pmode: "tsw".to_string(), seed: 1, report_secs: 30.0, mirror_slots: None, tb0: 0, sweep: None, wallgap_on: false, sym: false, selfcheck: false, wallgap: false, stop: None, deadline: None } }
}

struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } fn below(&mut self, n: u64) -> u64 { self.next() % n } }
fn hash64(vals: &[i128]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut h = std::collections::hash_map::DefaultHasher::new(); vals.hash(&mut h); h.finish()
}
fn luby(i: u64) -> u64 { // 1-based
    let mut i = i; loop { let mut k = 1u64; while (1u64 << k) - 1 < i { k += 1; } if (1u64 << k) - 1 == i { return 1u64 << (k - 1); } i -= (1u64 << (k - 1)) - 1; }
}

pub struct S<'a> {
    pub inst: &'a Instance, pub cfg: Cfg,
    pub placed: Vec<Tile>,
    grid: HashMap<i64, Vec<u32>>, cell: f64, stamp: Vec<u32>, stamp_ctr: u32,
    pub calls: u64, pub nodes_total: u64, pub jumps: u64, pub found: bool, pub found_tiles: Vec<[Pt; 3]>,
    pub keys: Vec<u32>, kset: HashMap<u32, usize>, pub nogoods: Vec<Vec<u32>>, pub ngtree: Vec<Rc<T>>, ngidx: HashMap<u32, Vec<usize>>, ngseen: HashSet<u128>, pub ng_hits: u64,
    kid: HashMap<u64, u32>, pub kkeys: Vec<Key>, khash: Vec<u64>, next_tick: u64,
    prog: Vec<(u32, u32)>, t0: Instant, pub secs_prev: f64, last_report: f64, pub maxdepth: usize, pub progpath: Option<String>,
    abort: bool, pub timed_out: bool, pub restarts: u64, pub stall_restarts: u64, pub luby_restarts: u64,
    calls_at_restart: u64, last_est: f64, frozen: u32, rng: Rng, sweep: Option<(i64, i64)>, shuffle: bool, tiebreak: u64,
    pub wallgap_kills: u64, pub selfchecked: u64, pub sym_apex: Option<Pt>, pub sym_skips: u64,
    pub gapset: Vec<bool>, // semigroup <a,b,c> membership of the integers 0..=max target side
    edge_iv: [Vec<(Q, Q, u32)>; 3], // per target edge: sorted disjoint intervals [start,end] covered by tile sides lying on it
    pub ck: Option<String>, pub ck_secs: f64, last_ck: f64,
    pub slice_end: u64, pub stopped: bool, pub slice_deadline: Option<Instant>, pub chk_mask: u64,
}

#[inline] fn bb_of(pts: &[Pt], sd: f64) -> [f64; 4] {
    let mut b = [f64::MAX, f64::MAX, f64::MIN, f64::MIN];
    for p in pts { let (x, y) = (p.fx(), p.fy(sd)); b[0] = b[0].min(x); b[1] = b[1].min(y); b[2] = b[2].max(x); b[3] = b[3].max(y); }
    b
}
const MARG: f64 = 1e-6;
#[inline] fn bb_over(a: &[f64; 4], b: &[f64; 4]) -> bool { a[0] <= b[2] + MARG && b[0] <= a[2] + MARG && a[1] <= b[3] + MARG && b[1] <= a[3] + MARG }
fn disjoint_tri(a: &[Pt; 3], b: &[Pt; 3]) -> bool {
    for (p, q) in [(a, b), (b, a)] {
        for i in 0..3 { if (0..3).all(|j| orient_sign(&p[i], &p[(i + 1) % 3], &q[j]) <= 0) { return true; } }
    }
    false
}
fn in_closed_tri(t: &[Pt; 3], p: &Pt) -> bool { (0..3).all(|i| orient_sign(&t[i], &t[(i + 1) % 3], p) >= 0) }

impl<'a> S<'a> {
    pub fn new(inst: &'a Instance, cfg: Cfg) -> S<'a> {
        let cell = inst.spec.sides.iter().cloned().max().unwrap() as f64 + 1.0;
        let seed = cfg.seed.max(1); let sweep0 = cfg.sweep; let tb0 = cfg.tb0;
        S { inst, cfg, placed: Vec::new(), grid: HashMap::default(), cell, stamp: Vec::new(), stamp_ctr: 0,
            calls: 0, nodes_total: 0, jumps: 0, found: false, found_tiles: Vec::new(),
            keys: Vec::new(), kset: HashMap::default(), nogoods: Vec::new(), ngtree: Vec::new(), ngidx: HashMap::default(), ngseen: HashSet::default(), ng_hits: 0,
            kid: HashMap::default(), kkeys: Vec::new(), khash: Vec::new(), next_tick: 0, prog: Vec::new(), t0: Instant::now(), secs_prev: 0.0, last_report: 0.0, maxdepth: 0, progpath: None,
            abort: false, timed_out: false, restarts: 0, stall_restarts: 0, luby_restarts: 0, calls_at_restart: 0, last_est: -1.0, frozen: 0,
            rng: Rng(seed.wrapping_mul(0x9E3779B97F4A7C15) | 1), sweep: sweep0, shuffle: false, tiebreak: tb0, wallgap_kills: 0, selfchecked: 0, sym_apex: None, sym_skips: 0, gapset: Vec::new(), edge_iv: [Vec::new(), Vec::new(), Vec::new()],
            ck: None, ck_secs: 120.0, last_ck: 0.0, slice_end: 0, stopped: false, slice_deadline: None, chk_mask: 255 }
    }
    fn secs(&self) -> f64 { self.secs_prev + self.t0.elapsed().as_secs_f64() }
    #[inline] fn sd(&self) -> f64 { self.inst.spec.sd }
    #[inline] fn dd(&self) -> i128 { self.inst.spec.dd }

    // ---------------- grid
    #[inline] fn crange(&self, bb: &[f64; 4]) -> (i64, i64, i64, i64) {
        (((bb[0] - MARG) / self.cell).floor() as i64, ((bb[2] + MARG) / self.cell).floor() as i64, ((bb[1] - MARG) / self.cell).floor() as i64, ((bb[3] + MARG) / self.cell).floor() as i64)
    }
    #[inline] fn ckey(x: i64, y: i64) -> i64 { (x << 32) ^ (y & 0xffff_ffff) }
    fn neighbors(&mut self, bb: &[f64; 4], out: &mut Vec<u32>) {
        out.clear();
        self.stamp_ctr = self.stamp_ctr.wrapping_add(1);
        if self.stamp_ctr == 0 { self.stamp.iter_mut().for_each(|s| *s = 0); self.stamp_ctr = 1; }
        if self.stamp.len() < self.placed.len() + 1 { self.stamp.resize(self.placed.len() + 64, 0); }
        let (x0, x1, y0, y1) = self.crange(bb);
        for x in x0..=x1 { for y in y0..=y1 {
            if let Some(l) = self.grid.get(&Self::ckey(x, y)) { for &i in l { if self.stamp[i as usize] != self.stamp_ctr { self.stamp[i as usize] = self.stamp_ctr; if bb_over(&self.placed[i as usize].bb, bb) { out.push(i); } } } }
        } }
    }
    fn kid_of(&mut self, tl: &[Pt; 3]) -> u32 {
        let mut v: Vec<&Pt> = tl.iter().collect(); v.sort_by(|a, b| a.x.cmp(&b.x).then(a.y.cmp(&b.y)));
        let mut h = Vec::with_capacity(12); for p in &v { h.push(p.x.n); h.push(p.x.d); h.push(p.y.n); h.push(p.y.d); }
        let hh = hash64(&h);
        if let Some(&i) = self.kid.get(&hh) { return i; }
        let sd = self.sd();
        let mut r: Vec<(i64, i64)> = tl.iter().map(|p| ((p.fx() * 1e4).round() as i64, (p.fy(sd) * 1e4).round() as i64)).collect(); r.sort();
        let i = self.kkeys.len() as u32; self.kkeys.push([r[0].0, r[0].1, r[1].0, r[1].1, r[2].0, r[2].1]); self.khash.push(hh); self.kid.insert(hh, i); i
    }
    fn make_tile(&self, o: &Opt, c: &Cand) -> Tile {
        let s = &self.inst.spec.slots[c.slot as usize];
        let d = o.d; let d2 = d.rot(s.psi, self.dd());
        let (l1, l2, l3) = (Q::int(s.l1), Q::int(s.l2), Q::int(s.l3));
        let e = Dir { c: l2.mul(d2.c).sub(l1.mul(d.c)).div(l3), s: l2.mul(d2.s).sub(l1.mul(d.s)).div(l3) };
        Tile { p: [o.v, c.p, c.q], rays: [d, d2, e, d.neg(), d2.neg(), e.neg()], bb: c.bb, slot: c.slot }
    }
    pub fn push_tile(&mut self, t: Tile) {
        let k = if self.cfg.ng { self.kid_of(&t.p) } else { 0 };
        let idx = self.placed.len();
        { let (x0, x1, y0, y1) = self.crange(&t.bb); for x in x0..=x1 { for y in y0..=y1 { self.grid.entry(Self::ckey(x, y)).or_default().push(idx as u32); } } }
        if self.cfg.ng { self.kset.insert(k, idx); self.keys.push(k); }
        if self.cfg.wallgap_on { self.add_edge_iv(&t, idx); }
        self.placed.push(t);
    }
    pub fn pop_tile(&mut self) {
        let t = self.placed.pop().unwrap();
        let idx = self.placed.len();
        if self.cfg.wallgap_on { for e in self.edge_iv.iter_mut() { if let Some(pos) = e.iter().rposition(|x| x.2 as usize == idx) { e.remove(pos); } } }
        { let (x0, x1, y0, y1) = self.crange(&t.bb); for x in x0..=x1 { for y in y0..=y1 { if let Some(l) = self.grid.get_mut(&Self::ckey(x, y)) { if let Some(pos) = l.iter().rposition(|&q| q as usize == idx) { l.swap_remove(pos); } } } } }
        if self.cfg.ng { let k = self.keys.pop().unwrap(); self.kset.remove(&k); }
    }

    // ---------------- corner / branch generation
    /// all admissible branches at the point v (appended to `out`)
    fn corner_opts(&mut self, v: Pt, out: &mut Vec<Rc<Opt>>) {
        let tgt = &self.inst.target;
        if !tgt.contains(&v) { return; }
        let dd = self.dd(); let sd = self.sd();
        // intervals: (start, end, halfplane?)
        let mut iv: Vec<(Dir, Dir, bool)> = Vec::with_capacity(12);
        let mut cmask = Mk::ZERO;
        for i in 0..3 {
            if orient_sign(&tgt.v[i], &tgt.v[(i + 1) % 3], &v) == 0 { iv.push((tgt.dir[i].neg(), tgt.dir[i], true)); }
        }
        let vb = [v.fx(), v.fy(sd), v.fx(), v.fy(sd)];
        let mut nb = Vec::new();
        self.neighbors(&vb, &mut nb);
        nb.sort();
        for &ti in &nb {
            let t = &self.placed[ti as usize];
            let os: [i32; 3] = [orient_sign(&t.p[0], &t.p[1], &v), orient_sign(&t.p[1], &t.p[2], &v), orient_sign(&t.p[2], &t.p[0], &v)];
            if os.iter().any(|&o| o < 0) { continue; }
            if os.iter().all(|&o| o > 0) { return; } // interior point of a tile: not a corner
            if let Some(k) = (0..3).find(|&k| t.p[k] == v) { iv.push((t.rays[2 * k], t.rays[2 * k + 1], false)); }
            else { let i = (0..3).find(|&i| os[i] == 0).unwrap(); iv.push((t.rays[2 * i], t.rays[2 * i].neg(), true)); }
            cmask |= tbit(ti as usize);
        }
        if iv.is_empty() { return; }
        // boundaries
        let mut u: Vec<Dir> = Vec::with_capacity(2 * iv.len());
        for &(s, e, _) in &iv { u.push(s); u.push(e); }
        u.sort_by(dir_cmp); u.dedup();
        let k = u.len();
        let contained = |x: &Dir| -> bool { iv.iter().any(|&(s, e, hp)| { if *x == s { return true; } if hp { s.cross_sign(x) > 0 } else { s.cross_sign(x) > 0 && x.cross_sign(&e) > 0 } }) };
        let free: Vec<bool> = (0..k).map(|i| !contained(&u[i])).collect(); // arc i = (u[i], u[i+1])
        if free.iter().all(|&f| f) { return; }
        let start = (0..k).find(|&i| !free[i]).unwrap();
        let mut arcs: Vec<(Dir, Dir, f64)> = Vec::new();
        let mut i = 0;
        while i < k {
            let idx = (start + i) % k;
            if free[idx] {
                let ds = u[idx]; let mut j = i; let mut last = idx;
                while j < k && free[(start + j) % k] { last = (start + j) % k; j += 1; }
                let de = u[(last + 1) % k];
                let a0 = ds.angle_f64(sd); let a1 = de.angle_f64(sd);
                let mut phi = a1 - a0; if phi <= 0.0 { phi += 2.0 * std::f64::consts::PI; }
                arcs.push((ds, de, phi));
                i = j;
            } else { i += 1; }
        }
        let na = arcs.len();
        let spec = &self.inst.spec;
        for ai in 0..na {
            let (d, dend, phi) = arcs[ai];
            let prev_end = arcs[(ai + na - 1) % na].1;
            if d.cross_sign(&prev_end) <= 0 { continue; } // not admissible (ext >= pi)
            let mut feas = Vec::new(); let mut blocked = Vec::new();
            let mut hits: Vec<u32> = Vec::new();
            for (slot, s) in spec.slots.iter().enumerate() {
                let e2 = d.rot(s.psi, dd);
                // psi <= phi  <=>  e2 within (d, dend]
                let fits = e2 == dend || (d.cross_sign(&e2) > 0 && e2.cross_sign(&dend) > 0);
                if !fits { continue; }
                let p = Pt::new(v.x.add(Q::int(s.l1).mul(d.c)), v.y.add(Q::int(s.l1).mul(d.s)));
                let q = Pt::new(v.x.add(Q::int(s.l2).mul(e2.c)), v.y.add(Q::int(s.l2).mul(e2.s)));
                if !self.inst.target.contains(&p) || !self.inst.target.contains(&q) { continue; }
                let tri = [v, p, q];
                let bb = bb_of(&tri, sd);
                let mut nb2 = Vec::new();
                self.neighbors(&bb, &mut nb2);
                hits.clear();
                for &ti in &nb2 { if !disjoint_tri(&self.placed[ti as usize].p, &tri) { hits.push(ti); } }
                if hits.is_empty() { feas.push(Cand { slot: slot as u8, p, q, bb }); }
                else { blocked.push(Cand { slot: slot as u8, p, q, bb }); }
            }
            out.push(Rc::new(Opt { v, d, dend, phi, feas, blocked, cmask }));
        }
    }

    pub fn root_opts(&mut self) -> Vec<Rc<Opt>> {
        let mut out = Vec::new();
        for i in 0..3 { let v = self.inst.target.v[i]; self.corner_opts(v, &mut out); }
        out
    }

    /// options after the tile with index `ti` (already pushed) was added to a state whose options were `parent`
    fn derive(&mut self, parent: &[Rc<Opt>], ti: usize) -> Vec<Rc<Opt>> {
        let tp = self.placed[ti].p; let tbb = self.placed[ti].bb;
        // affected points: vertices of the tile, vertices of neighbouring tiles lying in the closed tile, target vertices in it
        let mut aff: Vec<Pt> = tp.to_vec();
        let mut nb = Vec::new();
        self.neighbors(&tbb, &mut nb);
        for &u in &nb { if u as usize == ti { continue; } for k in 0..3 { let p = self.placed[u as usize].p[k]; if in_closed_tri(&tp, &p) && !aff.contains(&p) { aff.push(p); } } }
        for k in 0..3 { let p = self.inst.target.v[k]; if in_closed_tri(&tp, &p) && !aff.contains(&p) { aff.push(p); } }
        let mut out: Vec<Rc<Opt>> = Vec::with_capacity(parent.len() + 3);
        for o in parent {
            if aff.contains(&o.v) { continue; }
            // filter candidates against the new tile
            let mut elim: Vec<bool> = Vec::new(); let mut any = false;
            for c in &o.feas {
                let e = bb_over(&c.bb, &tbb) && !disjoint_tri(&[o.v, c.p, c.q], &tp);
                any |= e; elim.push(e);
            }
            if !any { out.push(o.clone()); continue; }
            let mut feas = Vec::with_capacity(o.feas.len()); let mut blocked = o.blocked.clone();
            for (c, &e) in o.feas.iter().zip(elim.iter()) { if e { blocked.push(c.clone()); } else { feas.push(c.clone()); } }
            blocked.sort_by_key(|c| c.slot);
            out.push(Rc::new(Opt { v: o.v, d: o.d, dend: o.dend, phi: o.phi, feas, blocked, cmask: o.cmask }));
        }
        for v in aff { self.corner_opts(v, &mut out); }
        out
    }

    fn add_edge_iv(&mut self, t: &Tile, idx: usize) {
        let dd = self.dd();
        for j in 0..3 {
            let (a, b) = (self.inst.target.v[j], self.inst.target.v[(j + 1) % 3]);
            let dir = self.inst.target.dir[j];
            for i in 0..3 {
                let (p, q) = (t.p[i], t.p[(i + 1) % 3]);
                if orient_sign(&a, &b, &p) == 0 && orient_sign(&a, &b, &q) == 0 {
                    let pos = |z: &Pt| -> Q { let u = z.sub(a); u.x.mul(dir.c).add(u.y.mul(dir.s).mul_int(dd)) };
                    let (mut s0, mut e0) = (pos(&p), pos(&q));
                    if s0 > e0 { std::mem::swap(&mut s0, &mut e0); }
                    let v = &mut self.edge_iv[j];
                    let at = v.iter().position(|x| x.0 > s0).unwrap_or(v.len());
                    v.insert(at, (s0, e0, idx as u32));
                }
            }
        }
    }
    /// target-edge gap rule: every maximal stretch of a target edge not covered by a tile side must be a sum of tile sides
    fn gap_conflict(&self) -> Option<Mk> {
        for j in 0..3 {
            let len = self.inst.target.len[j];
            let okf = |g: Q| -> bool { g.d == 1 && g.n >= 0 && (g.n as usize) < self.gapset.len() && self.gapset[g.n as usize] };
            let mut cur = Q::ZERO; let mut prev: Option<u32> = None;
            for &(s0, e0, ti) in &self.edge_iv[j] {
                let g = s0.sub(cur);
                if !okf(g) { let mut m = tbit(ti as usize); if let Some(p) = prev { m |= tbit(p as usize); } return Some(m); }
                cur = e0; prev = Some(ti);
            }
            let g = len.sub(cur);
            if !okf(g) { return Some(prev.map_or(Mk::ZERO, |p| tbit(p as usize))); }
        }
        None
    }
    fn fresh_mask(&mut self, o: &Opt) -> Mk {
        let mut mask = o.cmask;
        let mut hits: Vec<u32> = Vec::new();
        for c in &o.blocked {
            let tri = [o.v, c.p, c.q];
            let mut nb = Vec::new();
            self.neighbors(&c.bb, &mut nb);
            hits.clear();
            for &ti in &nb { if !disjoint_tri(&self.placed[ti as usize].p, &tri) { hits.push(ti); } }
            if hits.is_empty() { continue; }
            hits.sort();
            if !hits.iter().any(|&h| mask.has(h as usize)) { mask |= tbit(hits[0] as usize); }
        }
        mask
    }

    // ---------------- nogoods
    fn record(&mut self, tot: u64, m: Mk, tree: &Rc<T>) {
        if !self.cfg.ng || tot < 2 || self.nogoods.len() >= self.cfg.ngcap { return; }
        let mut ks: Vec<u32> = (0..self.placed.len()).filter(|&i| m.has(i)).map(|i| self.keys[i]).collect();
        if ks.is_empty() { return; }
        ks.sort();
        let h = Self::ng_hash(&ks);
        if self.ngseen.contains(&h) { return; }
        let id = self.nogoods.len();
        for k in &ks { self.ngidx.entry(*k).or_default().push(id); }
        self.ngseen.insert(h); self.nogoods.push(ks);
        if !self.cfg.notree { self.ngtree.push(tree.clone()); tree.def.set(Some(id)); }
    }
    fn lookup(&mut self) -> Option<(Mk, usize)> {
        if !self.cfg.ng || self.keys.is_empty() { return None; }
        let k = *self.keys.last().unwrap();
        if let Some(ids) = self.ngidx.get(&k) {
            for &id in ids {
                let mut m = Mk::ZERO; let mut ok = true;
                for kk in &self.nogoods[id] { match self.kset.get(kk) { Some(&i) => m |= tbit(i), None => { ok = false; break; } } }
                if ok { return Some((m, id)); }
            }
        }
        None
    }

    // ---------------- ordering
    fn tb(&self, o: &Opt) -> u64 { if self.tiebreak == 0 { 0 } else { hash64(&[o.v.x.n, o.v.x.d, o.v.y.n, o.v.y.d, self.tiebreak as i128]) } }
    fn sort_opts(&self, opts: &[Rc<Opt>]) -> Vec<Rc<Opt>> {
        let mut out: Vec<Rc<Opt>> = opts.to_vec();
        match self.cfg.order {
            Order::Lex => {
                let sw = self.sweep;
                let key = |o: &Rc<Opt>| -> (u8, Q, Q, Q) {
                    let alive = (!o.feas.is_empty()) as u8;
                    let rnd = if self.tiebreak != 0 { Q::int((self.tb(o) >> 8) as i128) } else { o.v.x };
                    match sw { None => (alive, o.v.y, rnd, Q::ZERO), Some((w1, w2)) => (alive, o.v.x.mul_int(w1 as i128).add(o.v.y.mul_int(w2 as i128)), o.v.y, rnd) }
                };
                out.sort_by(|a, b| key(a).cmp(&key(b)));
            }
            Order::Mrv => out.sort_by(|a, b| (a.feas.len(), a.phi).partial_cmp(&(b.feas.len(), b.phi)).unwrap().then_with(|| self.tb(a).cmp(&self.tb(b)))),
            Order::Band(band) => {
                let ymin = out.iter().map(|o| o.v.fy(self.sd())).fold(f64::MAX, f64::min);
                let key = |o: &Rc<Opt>| -> (usize, f64) { if o.feas.is_empty() { (0, 0.0) } else if o.v.fy(self.sd()) <= ymin + band { (o.feas.len(), o.phi) } else { (o.feas.len() + 1000, o.phi) } };
                out.sort_by(|a, b| key(a).partial_cmp(&key(b)).unwrap().then_with(|| self.tb(a).cmp(&self.tb(b))));
                if !out.is_empty() && !out[0].feas.is_empty() { out.retain(|o| o.v.fy(self.sd()) <= ymin + band); }
            }
        }
        out
    }
    fn tdir(&self, o: &Opt) -> ((f64, f64), (f64, f64)) { let sd = self.sd(); ((o.v.fx(), o.v.fy(sd)), (o.d.c.to_f64(), o.d.s.to_f64() * sd)) }

    fn est(&self) -> f64 { let mut est = 0.0f64; let mut w = 1.0f64; for &(i, n) in &self.prog { w /= n as f64; est += i as f64 * w; } est }

    fn check_events(&mut self) {
        // called every 256 main calls
        let secs = self.secs();
        if let Some(st) = &self.cfg.stop { if st.load(std::sync::atomic::Ordering::Relaxed) { self.abort = true; self.stopped = true; return; } }
        if let Some(dl) = self.cfg.deadline { if Instant::now() >= dl { self.abort = true; self.stopped = true; self.timed_out = true; return; } }
        if self.slice_end > 0 && self.calls >= self.slice_end { self.abort = true; return; }
        if let Some(sd) = self.slice_deadline { if Instant::now() >= sd { self.abort = true; return; } }
        if self.cfg.tl > 0.0 && secs >= self.cfg.tl { self.timed_out = true; self.abort = true; return; }
        if self.cfg.restart_unit > 0 {
            let budget = self.cfg.restart_unit * luby(self.luby_restarts + 1);
            if self.calls - self.calls_at_restart >= budget { self.abort = true; self.luby_restarts += 1; return; }
        }
        if self.cfg.stall_ticks > 0 && self.calls >= self.next_tick {
            self.next_tick = self.calls + self.cfg.tick;
            let e = self.est();
            if (e - self.last_est).abs() < 1e-9 { self.frozen += 1; } else { self.frozen = 0; }
            self.last_est = e;
            if self.frozen >= self.cfg.stall_ticks { self.abort = true; self.stall_restarts += 1; return; }
        }
        if secs >= self.last_report + self.cfg.report_secs {
            self.last_report = secs;
            let head: Vec<String> = self.prog.iter().take(14).map(|&(i, n)| format!("{}/{}", i, n)).collect();
            let line = format!("secs={:.0} calls={} depth={} maxdepth={} nogoods={} hits={} restarts={} est={:.6}% path={}", secs, self.calls, self.placed.len(), self.maxdepth, self.nogoods.len(), self.ng_hits, self.restarts, self.est() * 100.0, head.join(" "));
            if let Some(p) = &self.progpath { use std::io::Write; if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(p) { let _ = writeln!(f, "{}", line); } } else { eprintln!("{}", line); }
        }
        if let Some(ck) = self.ck.clone() { if secs >= self.last_ck + self.ck_secs { self.save_ck(&ck); self.last_ck = secs; } }
    }

    // ---------------- the search
    /// half-triangle symmetry: with the reflection sigma fixing the apex A (equal adjacent sides), a tiling and its mirror have root
    /// slot pairs (s,u) and (u,s), where s = slot of the tile flush with the first wall at A and u = slot^1 of the tile flush with the
    /// second wall; keep only s <= u.  Returns false when the candidate (which fills the last gap at A) violates s <= u.
    fn sym_ok(&self, o: &Opt, c: &Cand) -> bool {
        let a = match self.sym_apex { Some(a) => a, None => return true };
        if o.v != a { return true; }
        let sl = &self.inst.spec.slots[c.slot as usize];
        let e2 = o.d.rot(sl.psi, self.dd());
        if e2 != o.dend { return true; } // does not fill the corner
        let s_root = if self.placed.is_empty() { c.slot } else { self.placed[0].slot };
        (c.slot ^ 1) >= s_root
    }
    fn check_incremental(&mut self, opts: &[Rc<Opt>]) {
        let mut pts: Vec<Pt> = self.inst.target.v.to_vec();
        for t in &self.placed { for p in &t.p { if !pts.contains(p) { pts.push(*p); } } }
        let mut full: Vec<Rc<Opt>> = Vec::new();
        for p in pts { self.corner_opts(p, &mut full); }
        let sig = |o: &Rc<Opt>| format!("{:?}|{:?}|{:?}|{:?}", o.v, o.d, o.feas.iter().map(|c| c.slot).collect::<Vec<_>>(), o.blocked.iter().map(|c| c.slot).collect::<Vec<_>>());
        let mut a: Vec<String> = opts.iter().map(sig).collect(); let mut b: Vec<String> = full.iter().map(sig).collect();
        a.sort(); b.sort();
        if a != b { panic!("INCREMENTAL MISMATCH at depth {}:\n inc={:?}\n full={:?}", self.placed.len(), a, b); }
        // dead-end conflict sets: the incremental mask must be a SUPERSET-correct reason; here we only require both agree on emptiness
        self.selfchecked += 1;
    }
    fn solve(&mut self, opts: &[Rc<Opt>], limit: u32, main: bool) -> R {
        if self.found || self.abort { return None; }
        if self.cfg.selfcheck { self.check_incremental(opts); }
        self.nodes_total += 1;
        if main {
            self.calls += 1;
            if self.calls >= self.cfg.cap { self.abort = true; return None; }
            if self.placed.len() > self.maxdepth { self.maxdepth = self.placed.len(); }
            if self.calls & self.chk_mask == 0 { self.check_events(); if self.abort { return None; } }
        }
        if self.cfg.wallgap_on { if let Some(m) = self.gap_conflict() { self.wallgap_kills += 1; return Some((1, m, mk((0.0, 0.0), (0.0, 0.0), vec![]))); } }
        let mut sorted = self.sort_opts(opts);
        if let Some(a) = self.sym_apex { if self.placed.is_empty() { let mut s2: Vec<Rc<Opt>> = sorted.iter().filter(|o| o.v == a).cloned().collect(); if !s2.is_empty() { std::mem::swap(&mut sorted, &mut s2); } } }
        if sorted.is_empty() {
            if self.placed.len() == self.inst.n && main { self.found = true; self.found_tiles = self.placed.iter().map(|t| t.p).collect(); }
            return None;
        }
        let depth = self.placed.len();
        let bit = tbit(depth);
        let clr: Mk = if depth <= MBITS - 1 { !bit } else { Mk::ONES };
        if let Some((m, id)) = self.lookup() { self.ng_hits += 1; return Some((1, m, Rc::new(T { v: (0.0, 0.0), d: (0.0, 0.0), kids: vec![], stub: Some(id), def: Cell::new(None) }))); }
        if sorted[0].feas.is_empty() {
            let mut best: Option<(Mk, Rc<Opt>)> = None;
            for o in sorted.iter().filter(|o| o.feas.is_empty()) {
                let m = self.fresh_mask(o);
                if best.as_ref().map_or(true, |(bm, _)| (m.count_ones(), m.top()) < (bm.count_ones(), bm.top())) { best = Some((m, o.clone())); }
            }
            let (bm, bo) = best.unwrap();
            let (v, d) = self.tdir(&bo);
            return Some((1, bm, mk(v, d, vec![])));
        }
        if limit == 0 { return None; }
        let notree = self.cfg.notree;
        if !main {
            let mut best: R = None;
            for o in &sorted {
                let mut tot = 1u64; let mut m = Mk::ZERO; let mut ok = true; let mut kids = Vec::new();
                let (tv, td) = self.tdir(o);
                for c in &o.feas {
                    if !self.sym_ok(o, c) { self.sym_skips += 1; m |= tbit(0); continue; }
                    let t = self.make_tile(o, c);
                    self.push_tile(t);
                    let child = self.derive(opts, depth);
                    let r = self.solve(&child, limit - 1, false);
                    self.pop_tile();
                    match r {
                        None => { ok = false; break; }
                        Some((s, mm, tr)) => {
                            if self.cfg.cbj && (mm & bit).is_zero() { self.jumps += 1; return Some((s, mm, tr)); }
                            tot += s; m |= mm & clr; if !notree { kids.push((c.slot as usize, tr)); }
                        }
                    }
                }
                if ok { m |= self.fresh_mask(o); }
                if ok && best.as_ref().map_or(true, |b| tot < b.0) { best = Some((tot, m, mk(tv, td, kids))); }
            }
            if let Some((tot, m, tr)) = &best { let (a, b, c) = (*tot, *m, tr.clone()); self.record(a, b, &c); }
            return best;
        }
        // main call: choose the branch
        let mut bi = 0usize; let mut bscore = u64::MAX; let mut bests: Vec<R> = Vec::new();
        if self.cfg.la > 0 && !matches!(self.cfg.order, Order::Lex) {
            for (i, o) in sorted.iter().enumerate() {
                let mut sc = 0u64; let mut ests: Vec<R> = Vec::new();
                for c in &o.feas {
                    if !self.sym_ok(o, c) { self.sym_skips += 1; continue; }
                    let t = self.make_tile(o, c);
                    self.push_tile(t);
                    let child = self.derive(opts, depth);
                    let r = self.solve(&child, self.cfg.la, false);
                    self.pop_tile();
                    if self.abort { return None; }
                    if let Some((_, mm, _)) = &r { if self.cfg.cbj && (*mm & bit).is_zero() { self.jumps += 1; return r; } }
                    sc += match &r { Some(x) => x.0, None => self.cfg.w };
                    ests.push(r);
                    if sc >= bscore { break; }
                }
                if sc < bscore { bscore = sc; bi = i; bests = ests; }
            }
        }
        let o = sorted[bi].clone();
        let mut order: Vec<usize> = (0..o.feas.len()).collect();
        if depth == 0 { if let Some(rs) = &self.cfg.mirror_slots { order.retain(|&i| rs.contains(&(o.feas[i].slot as usize))); } }
        if self.shuffle && depth > 0 && order.len() > 1 { for i in (1..order.len()).rev() { let j = self.rng.below(i as u64 + 1) as usize; order.swap(i, j); } }
        let mut tot = 1u64; let mut m = self.fresh_mask(&o); let mut kids = Vec::new();
        let nfeas = o.feas.len() as u32;
        let (tv, td) = self.tdir(&o);
        let mut bests: Vec<Option<R>> = if bests.is_empty() { Vec::new() } else { bests.into_iter().map(Some).collect() };
        for (pos, &idx) in order.iter().enumerate() {
            let c = &o.feas[idx];
            if !self.sym_ok(&o, c) { self.sym_skips += 1; m |= tbit(0); continue; }
            let pre: Option<(u64, Mk, Rc<T>)> = if idx < bests.len() && !self.shuffle { bests[idx].take().flatten() } else { None };
            let r = if pre.is_some() { pre } else {
                let t = self.make_tile(&o, c);
                self.push_tile(t);
                self.prog.push((pos as u32, nfeas));
                let child = self.derive(opts, depth);
                let r = self.solve(&child, u32::MAX, true);
                self.prog.pop();
                self.pop_tile();
                r
            };
            match r {
                None => return None,
                Some((s, mm, tr)) => {
                    if self.cfg.cbj && (mm & bit).is_zero() { self.jumps += 1; return Some((s, mm, tr)); }
                    tot += s; m |= mm & clr; if !notree { kids.push((c.slot as usize, tr)); }
                }
            }
        }
        let tr = mk(tv, td, kids);
        self.record(tot, m, &tr);
        Some((tot, m, tr))
    }

    pub fn save_ck_pub(&self, ck: &str) { self.save_ck(ck) }
    fn save_ck(&self, ck: &str) {
        // verdict-mode checkpoint: the learned nogoods; resuming = a restart with nogood retention (the DFS stack is not saved)
        let mut o = format!("bteck 2\ncalls {} secs {:.1} restarts {}\n", self.calls, self.secs(), self.restarts);
        for (i, k) in self.kkeys.iter().enumerate() { o.push_str(&format!("k {} {} {} {} {} {} {}\n", self.khash[i], k[0], k[1], k[2], k[3], k[4], k[5])); }
        for g in &self.nogoods { o.push_str("g"); for k in g { o.push_str(&format!(" {}", k)); } o.push('\n'); }
        let tmp = format!("{}.tmp", ck);
        if std::fs::write(&tmp, o).is_ok() { let _ = std::fs::rename(&tmp, ck); }
    }
    pub fn load_ck(&mut self, ck: &str) -> bool {
        let txt = match std::fs::read_to_string(ck) { Ok(t) => t, Err(_) => return false };
        let mut lines = txt.lines();
        if lines.next() != Some("bteck 2") { return false; }
        let hdr: Vec<&str> = lines.next().unwrap_or("").split_whitespace().collect();
        if hdr.len() >= 6 { self.calls = hdr[1].parse().unwrap_or(0); self.secs_prev = hdr[3].parse().unwrap_or(0.0); self.restarts = hdr[5].parse::<u64>().unwrap_or(0) + 1; }
        for l in lines {
            let w: Vec<&str> = l.split_whitespace().collect();
            if w.is_empty() { continue; }
            if w[0] == "k" {
                let h: u64 = w[1].parse().unwrap(); let id = self.kkeys.len() as u32;
                self.kkeys.push([w[2].parse().unwrap(), w[3].parse().unwrap(), w[4].parse().unwrap(), w[5].parse().unwrap(), w[6].parse().unwrap(), w[7].parse().unwrap()]);
                self.khash.push(h); self.kid.insert(h, id);
            } else if w[0] == "g" {
                let ks: Vec<u32> = w[1..].iter().map(|x| x.parse().unwrap()).collect();
                let id = self.nogoods.len(); for k in &ks { self.ngidx.entry(*k).or_default().push(id); }
                self.ngseen.insert(Self::ng_hash(&ks));
                self.nogoods.push(ks);
            }
        }
        true
    }
    fn ng_hash(ks: &[u32]) -> u128 { use std::hash::{Hash, Hasher}; let mut h1 = std::collections::hash_map::DefaultHasher::new(); ks.hash(&mut h1); let mut h2 = std::collections::hash_map::DefaultHasher::new(); 0x9e3779b97f4a7c15u64.hash(&mut h2); ks.hash(&mut h2); ((h1.finish() as u128) << 64) | h2.finish() as u128 }

    /// run to completion; returns Some(tree) if refuted, None if found / aborted
    pub fn run(&mut self) -> (R, &'static str) {
        self.t0 = Instant::now();
        let root = self.root_opts();
        if self.cfg.wallgap_on {
            let mx = self.inst.target.len.iter().map(|l| l.n / l.d).max().unwrap().max(0);
            if mx > 4_000_000 || self.inst.target.len.iter().any(|l| l.d != 1) { eprintln!("--wallgap ignored: non-integer or huge target sides"); self.cfg.wallgap_on = false; }
            else {
                let mut ok = vec![false; (mx + 1) as usize]; ok[0] = true;
                for g in 1..=(mx as usize) { for &sd in &self.inst.spec.sides { let sd = sd as usize; if g >= sd && ok[g - sd] { ok[g] = true; break; } } }
                self.gapset = ok;
            }
        }
        if self.cfg.sym {
            let t = &self.inst.target;
            self.sym_apex = (0..3).find(|&i| t.len[i] == t.len[(i + 2) % 3]).map(|i| t.v[i]);
            if self.sym_apex.is_none() { eprintln!("--sym ignored: the target is scalene"); }
        }
        loop {
            self.abort = false;
            self.calls_at_restart = self.calls; self.frozen = 0; self.last_est = -1.0;
            let r = self.solve(&root, u32::MAX, true);
            if self.found { return (None, "FOUND"); }
            if self.timed_out { return (None, "TIMEOUT"); }
            if self.calls >= self.cfg.cap { return (None, "CAPPED"); }
            if !self.abort { return match r { Some(_) => (r, "NO_TILING"), None => (None, "CAPPED") }; }
            // restart with retained nogoods and a new order
            self.restarts += 1;
            self.prog.clear();
            if self.cfg.perturb {
                if self.cfg.pmode.contains('t') { self.tiebreak = self.rng.next() | 1; }
                if self.cfg.pmode.contains('s') { self.shuffle = true; }
                if self.cfg.pmode.contains('w') && matches!(self.cfg.order, Order::Lex) {
                    let w = [(1, 0), (0, 1), (1, 1), (1, -1), (-1, 1), (0, -1), (-1, 0), (2, 1), (1, 2), (-1, -1), (2, -1), (1, -2)];
                    self.sweep = Some(w[(self.rng.below(w.len() as u64)) as usize]);
                }
            }
            if self.cfg.report_secs < 1e8 { eprintln!("restart {} at calls={} secs={:.0} nogoods={} sweep={:?}", self.restarts, self.calls, self.secs(), self.nogoods.len(), self.sweep); }
        }
    }

    /// portfolio: one slice of at most `budget` main calls from the root with the current cfg order / tie-break.  Nogoods persist
    /// across slices (they are semantic: sets of tile keys, valid under every order).  Returns FOUND, NO_TILING (the slice finished
    /// without abort: a COMPLETE exhaustive search of this orientation), STOP (external stop / deadline) or SLICE (budget used).
    pub fn run_slice(&mut self, root: &[Rc<Opt>], budget: u64, secs: f64) -> &'static str {
        self.abort = false; self.prog.clear(); self.frozen = 0;
        self.slice_end = if budget > 0 { self.calls + budget } else { 0 }; self.calls_at_restart = self.calls;
        self.slice_deadline = if secs > 0.0 { Some(Instant::now() + std::time::Duration::from_secs_f64(secs)) } else { None };
        self.chk_mask = if self.cfg.la > 0 && !matches!(self.cfg.order, Order::Lex) { 7 } else { 255 };
        let r = self.solve(root, u32::MAX, true);
        self.prog.clear();
        if self.found { return "FOUND"; }
        if self.stopped { return "STOP"; }
        if self.abort { return "SLICE"; }
        match r { Some(_) => "NO_TILING", None => "SLICE" }
    }
    pub fn set_shuffle(&mut self, b: bool) { self.shuffle = b; }
    pub fn set_tb(&mut self, t: u64) { self.tiebreak = t | 1; }
    pub fn rnd(&mut self) -> u64 { self.rng.next() }

    /// write the proof tree in the mrv2/certgenx format
    pub fn write_tree(&self, tree: &Rc<T>, path: &str) -> u64 {
        let mut refs: HashSet<usize> = HashSet::default();
        collect(tree, &mut refs, &self.ngtree);
        let mut o = String::from("M\n");
        let mut cert = emit(tree, true, &refs, &self.ngtree, &mut o);
        let mut ids: Vec<usize> = refs.iter().cloned().collect(); ids.sort();
        for id in ids {
            o.push_str(&format!("N {} {}\n", id, self.nogoods[id].len()));
            let mut kk: Vec<Key> = self.nogoods[id].iter().map(|&i| self.kkeys[i as usize]).collect(); kk.sort();
            for k in &kk { o.push_str(&format!("{} {} {} {} {} {}\n", k[0] as f64 / 1e4, k[1] as f64 / 1e4, k[2] as f64 / 1e4, k[3] as f64 / 1e4, k[4] as f64 / 1e4, k[5] as f64 / 1e4)); }
            cert += emit(&self.ngtree[id], true, &refs, &self.ngtree, &mut o);
        }
        if path != "-" { let tmp = format!("{}.tmp", path); std::fs::write(&tmp, o).unwrap(); std::fs::rename(&tmp, path).unwrap(); }
        cert
    }
}
