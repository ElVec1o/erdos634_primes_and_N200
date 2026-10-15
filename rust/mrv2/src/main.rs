// mrv2: MEASUREMENT prototype (f64 + eps), not a proof engine.
// Corner-fill refutation search with (1) free convex-corner branching chosen by bounded lookahead,
// (2) dependency tracking (conflict sets) and proof-tree trimming / backjumping.
// Usage: mrv2 <ta> <tb> <tc> <Ta> <Tb> <Tc> <N> <la> <cbj:0|1> [cap] [W]
// Conflict masks have 512 bits (see `Mk`).
// Checkpoints: MRV_CKPT=<prefix> makes the run resumable.  Every MRV_CKPT_SECS
// seconds (default 120) the state is saved: <prefix>.nodes and <prefix>.ng are append-only logs (finished subtrees,
// tile keys and nogoods), <prefix>.dead the dead regions (MRV_REGION), and <prefix>.path (replaced atomically) holds
// the counters, the valid lengths of the logs and the DFS frames.  A run started with the same arguments resumes from
// <prefix>.path; a finished run leaves <prefix>.result (one line) and a rerun prints it and exits.  MRV_TL=<secs> is
// a CUMULATIVE time limit (all segments): on expiry the state is saved and the verdict printed is TIMEOUT.
// A checkpoint written in tree mode can be resumed with MRV_NOTREE=1 (verdict only, small memory).
use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use std::env;
const EPS: f64 = 1e-7;
type P = (f64, f64);
fn sub(a: P, b: P) -> P { (a.0 - b.0, a.1 - b.1) }
fn cross(a: P, b: P) -> f64 { a.0 * b.1 - a.1 * b.0 }
fn dot(a: P, b: P) -> f64 { a.0 * b.0 + a.1 * b.1 }
fn norm(a: P) -> f64 { dot(a, a).sqrt() }
fn orient(a: P, b: P, c: P) -> f64 { cross(sub(b, a), sub(c, a)) }
#[derive(Clone, Copy)]
struct Tri { p: [P; 3], c: [P; 3] } // c: the Galois-conjugate triangle (= p when conjugate pruning is off)
#[derive(Clone)]
struct Opt { v: P, d: f64, phi: f64, feas: Vec<(usize, Tri)>, mask: Mk }
struct T { v: P, d: f64, kids: Vec<(usize, Rc<T>)>, stub: Option<usize>, def: Cell<Option<usize>>, sid: Cell<u64> } // sid: id in the checkpoint node log (0 = not saved)
#[derive(Clone)]
struct Frame { v: P, d: f64, nfeas: u32, done: Vec<(usize, u64, Mk, Rc<T>)> } // one main level of the DFS: branch (v, d) and its finished children (slot, size, mask, tree)
type R = Option<(u64, Mk, Rc<T>)>;
fn mk(v: P, d: f64, kids: Vec<(usize, Rc<T>)>) -> Rc<T> { Rc::new(T { v, d, kids, stub: None, def: Cell::new(None), sid: Cell::new(0) }) }
/// Conflict masks: one bit per placed tile, MBITS = 512 bits.  The tiles numbered MBITS - 1
/// and above SHARE the last bit, which then means "some tile numbered MBITS - 1 or more" and is cleared only at
/// depth MBITS - 1; this is conservative.
const MW: usize = 8;
const MBITS: usize = MW * 64;
#[derive(Clone, Copy, PartialEq, Eq)]
struct Mk([u64; MW]);
impl Mk {
    const ZERO: Mk = Mk([0; MW]);
    const ONES: Mk = Mk([!0u64; MW]);
    fn is_zero(&self) -> bool { self.0.iter().all(|&w| w == 0) }
    fn count_ones(&self) -> u32 { self.0.iter().map(|w| w.count_ones()).sum() }
    /// number of the highest set bit, plus one (0 for the empty mask)
    fn top(&self) -> u32 { for k in (0..MW).rev() { if self.0[k] != 0 { return (k as u32) * 64 + 64 - self.0[k].leading_zeros(); } } 0 }
    /// the bits 0 .. i-1 (everything for i >= MBITS)
    fn below(i: usize) -> Mk { let mut m = [0u64; MW]; for k in 0..MW { let lo = k * 64; if i >= lo + 64 { m[k] = !0; } else if i > lo { m[k] = (1u64 << (i - lo)) - 1; } } Mk(m) }
    fn hex(&self) -> String { let mut o = String::new(); for k in (0..MW).rev() { o.push_str(&format!("{:016x}", self.0[k])); } o }
    fn from_hex(x: &str) -> Mk { let mut m = [0u64; MW]; for k in 0..MW { let a = (MW - 1 - k) * 16; m[k] = u64::from_str_radix(&x[a..a + 16], 16).unwrap(); } Mk(m) }
}
impl std::ops::BitOr for Mk { type Output = Mk; fn bitor(self, o: Mk) -> Mk { let mut m = self.0; for k in 0..MW { m[k] |= o.0[k]; } Mk(m) } }
impl std::ops::BitAnd for Mk { type Output = Mk; fn bitand(self, o: Mk) -> Mk { let mut m = self.0; for k in 0..MW { m[k] &= o.0[k]; } Mk(m) } }
impl std::ops::Not for Mk { type Output = Mk; fn not(self) -> Mk { let mut m = self.0; for k in 0..MW { m[k] = !m[k]; } Mk(m) } }
impl std::ops::BitOrAssign for Mk { fn bitor_assign(&mut self, o: Mk) { for k in 0..MW { self.0[k] |= o.0[k]; } } }
fn tbit(i: usize) -> Mk { let i = i.min(MBITS - 1); let mut m = [0u64; MW]; m[i / 64] = 1u64 << (i % 64); Mk(m) }
fn hash128(ks: &[u32]) -> u128 {
    use std::hash::{Hash, Hasher};
    let mut h1 = std::collections::hash_map::DefaultHasher::new(); ks.hash(&mut h1);
    let mut h2 = std::collections::hash_map::DefaultHasher::new(); 0x9e3779b97f4a7c15u64.hash(&mut h2); ks.hash(&mut h2);
    ((h1.finish() as u128) << 64) | (h2.finish() as u128)
}
/// append the unsaved nodes of `t` to the node log (children first); returns the log id of `t`
fn save_tree(t: &T, next: &mut u64, out: &mut String) -> u64 {
    let s = t.sid.get(); if s != 0 { return s; }
    let ks: Vec<(usize, u64)> = t.kids.iter().map(|(slot, k)| (*slot, save_tree(k, next, out))).collect();
    *next += 1; t.sid.set(*next);
    out.push_str(&format!("{:016x} {:016x} {:016x} {} {} {}", t.v.0.to_bits(), t.v.1.to_bits(), t.d.to_bits(),
        t.stub.map_or(-1, |x| x as i64), t.def.get().map_or(-1, |x| x as i64), ks.len()));
    for (slot, c) in ks { out.push_str(&format!(" {} {}", slot, c)); }
    out.push('\n');
    *next
}
fn append_sync(path: &str, data: &str) -> u64 {
    use std::io::Write;
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).unwrap();
    f.write_all(data.as_bytes()).unwrap(); f.sync_all().unwrap();
    data.len() as u64
}
fn truncate_to(path: &str, len: u64) {
    if let Ok(f) = std::fs::OpenOptions::new().write(true).create(true).open(path) { f.set_len(len).unwrap(); f.sync_all().unwrap(); }
}
fn collect(t: &T, refs: &mut HashSet<usize>, table: &[Rc<T>]) {
    if let Some(id) = t.stub { if refs.insert(id) { collect(&table[id], refs, table); } return; }
    for (_, k) in &t.kids { collect(k, refs, table); }
}
fn tsize(t: &T) -> u64 { 1 + t.kids.iter().map(|(_, k)| tsize(k)).sum::<u64>() }
/// reference counts of the nogoods in the emitted structure (def sites of referenced nogoods count as references)
fn count(t: &T, root: bool, refs: &HashSet<usize>, cnt: &mut HashMap<usize, u32>, table: &[Rc<T>]) {
    let rid = if let Some(id) = t.stub { Some(id) } else if !root { t.def.get().filter(|id| refs.contains(id)) } else { None };
    if let Some(id) = rid {
        let c = cnt.entry(id).or_insert(0); *c += 1;
        if *c == 1 { count(&table[id], true, refs, cnt, table); }
        return;
    }
    for (_, k) in &t.kids { count(k, false, refs, cnt, table); }
}
/// returns the number of emitted lines (= certificate nodes); `piece` = nogoods emitted as separate pieces
fn emit(t: &T, root: bool, refs: &HashSet<usize>, piece: &HashSet<usize>, table: &[Rc<T>], out: &mut String) -> u64 {
    let rid = if let Some(id) = t.stub { Some(id) } else if !root { t.def.get().filter(|id| refs.contains(id)) } else { None };
    if let Some(id) = rid {
        if piece.contains(&id) { out.push_str(&format!("S {}\n", id)); return 1; }
        return emit(&table[id], true, refs, piece, table, out);
    }
    let mut sl = [0u8; 6];
    for (i, _) in &t.kids { sl[*i] = 1; }
    out.push_str(&format!("T {:.12} {:.12} {:.12} {:.12} {} {} {} {} {} {}\n", t.v.0, t.v.1, t.d.cos(), t.d.sin(), sl[0], sl[1], sl[2], sl[3], sl[4], sl[5]));
    let mut n = 1;
    for (_, k) in &t.kids { n += emit(k, false, refs, piece, table, out); }
    n
}
type Key = [i64; 6];
fn key(t: &Tri) -> Key {
    let mut v: Vec<(i64, i64)> = t.p.iter().map(|p| ((p.0 * 1e4).round() as i64, (p.1 * 1e4).round() as i64)).collect();
    v.sort();
    [v[0].0, v[0].1, v[1].0, v[1].1, v[2].0, v[2].1]
}
struct S {
    tgt: Vec<P>, ang: [f64; 3], side: [f64; 3], n: usize,
    placed: Vec<Tri>,
    calls: u64, cap: u64, found: bool, la: u32, w: u64, cbj: bool, jumps: u64,
    mode: u8, band: f64, conj: bool, conj_kills: u64, found_tiles: Vec<Tri>,
    ng: bool, keys: Vec<u32>, kset: HashMap<u32, usize>, nogoods: Vec<Vec<u32>>, ngtree: Vec<Rc<T>>, ngidx: HashMap<u32, Vec<usize>>, ngseen: HashSet<u128>, ng_hits: u64,
    kid: HashMap<Key, u32>, kkeys: Vec<Key>, // tile keys interned (a nogood is a sorted list of key ids)
    // checkpoint state (MRV_CKPT)
    frames: Vec<Frame>, resume: Vec<Frame>, ck: Option<String>, ck_secs: u64, last_ck: u64, secs_prev: u64, tl: u64, sig: String,
    ck_ng_saved: usize, ck_keys_saved: usize, dead_log: Vec<u128>, next_sid: u64, len_nodes: u64, len_ng: u64, len_dead: u64, ck_count: u64,
    // progress estimate of the main DFS (MRV_PROGRESS=<file>): path of (child index, branching) pairs
    prog: Vec<(u32, u32)>, t_start: std::time::Instant, last_report: u64, maxdepth: usize, progpath: Option<String>,
    rootslots: Option<Vec<usize>>, // MRV_ROOTSLOTS="4,5": at the root keep only these slots (NOT a refutation of the whole instance). Verdict only, unless MRV_ROOTTREE=1: then the tree of the kept slots is written, for rust/certgenx in MIRROR mode, which refutes the other live root slots through Refl.sound_mirror
    notree: bool, region: bool, dead: HashSet<u128>, rg_hits: u64, // MRV_NOTREE: do not keep the tree (verdict only); MRV_REGION: memoize dead uncovered regions (measurement only, no certificate)
    ngcap: usize, // MRV_NGCAP: stop recording new nogoods beyond this number (memory bound; the tree stays valid) // 0 = most-constrained anywhere, 1 = lowest corner (sweep), 2 = most-constrained within a band above the lowest corner
}
fn in_closed(t: &[P], q: P) -> bool {
    for i in 0..t.len() { if orient(t[i], t[(i + 1) % t.len()], q) < -EPS { return false; } }
    true
}
fn overlap(a: &Tri, b: &Tri) -> bool {
    for (x, y) in [(a, b), (b, a)] {
        for i in 0..3 {
            let (p, q) = (x.p[i], x.p[(i + 1) % 3]);
            let l = norm(sub(q, p));
            if (0..3).all(|j| orient(p, q, y.p[j]) / l <= EPS) { return false; }
        }
    }
    true
}
fn overlap_c(a: &Tri, b: &Tri) -> bool {
    for (x, y) in [(a, b), (b, a)] {
        for i in 0..3 {
            let (p, q) = (x.c[i], x.c[(i + 1) % 3]);
            let l = norm(sub(q, p));
            if (0..3).all(|j| orient(p, q, y.c[j]) / l <= EPS) { return false; }
        }
    }
    true
}
fn norm_ang(mut a: f64) -> f64 {
    let t = 2.0 * std::f64::consts::PI;
    while a < 0.0 { a += t; }
    while a >= t { a -= t; }
    a
}
impl S {
    fn kid_of(&mut self, k: Key) -> u32 { if let Some(&i) = self.kid.get(&k) { i } else { let i = self.kkeys.len() as u32; self.kkeys.push(k); self.kid.insert(k, i); i } }
    fn push(&mut self, t: Tri) { if self.ng { let k = self.kid_of(key(&t)); self.kset.insert(k, self.placed.len()); self.keys.push(k); } self.placed.push(t); }
    fn mark_dead(&mut self, k: u128) { if self.dead.insert(k) && self.ck.is_some() { self.dead_log.push(k); } }
    fn secs(&self) -> u64 { self.secs_prev + self.t_start.elapsed().as_secs() }
    fn pop(&mut self) { if self.ng { let k = self.keys.pop().unwrap(); self.kset.remove(&k); } self.placed.pop(); }
    fn record(&mut self, tot: u64, m: Mk, tree: &Rc<T>) {
        if !self.ng || tot < 2 || self.nogoods.len() >= self.ngcap { return; }
        let mut ks: Vec<u32> = (0..self.placed.len()).filter(|i| !(m & tbit(*i)).is_zero()).map(|i| self.keys[i]).collect();
        if ks.is_empty() { return; }
        ks.sort();
        let h = hash128(&ks);
        if self.ngseen.contains(&h) { return; }
        let id = self.nogoods.len();
        for k in &ks { self.ngidx.entry(*k).or_default().push(id); }
        self.ngseen.insert(h);
        self.nogoods.push(ks);
        self.ngtree.push(tree.clone());
        tree.def.set(Some(id));
    }
    fn lookup(&mut self) -> Option<(Mk, usize)> {
        if !self.ng || self.keys.is_empty() { return None; }
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
    /// conjugate frame of the branch (v, d): the conjugate point of `v` and the conjugate of the direction `d`.
    /// `v` is a target vertex or a vertex of a placed tile; `d` runs along a target edge or a tile edge through `v`.
    fn conj_frame(&self, v: P, d: f64) -> Option<(P, f64)> {
        let pi = std::f64::consts::PI;
        let same = |a: f64, b: f64| { let x = norm_ang(a - b); x < 1e-6 || x > 2.0 * pi - 1e-6 };
        let mut cv: Option<P> = None;
        for i in 0..self.tgt.len() { if norm(sub(self.tgt[i], v)) <= EPS { cv = Some(v); } }
        if cv.is_none() { 'f: for t in &self.placed { for k in 0..3 { if norm(sub(t.p[k], v)) <= EPS { cv = Some(t.c[k]); break 'f; } } } }
        let cv = cv?;
        for i in 0..self.tgt.len() {
            let (p, q) = (self.tgt[i], self.tgt[(i + 1) % self.tgt.len()]);
            if (orient(p, q, v) / norm(sub(q, p))).abs() > EPS { continue; }
            let a = (q.1 - p.1).atan2(q.0 - p.0);
            if same(a, d) || same(a + pi, d) { return Some((cv, d)); }
        }
        for t in &self.placed {
            for i in 0..3 {
                let (p, q) = (t.p[i], t.p[(i + 1) % 3]);
                if (orient(p, q, v) / norm(sub(q, p))).abs() > EPS { continue; }
                let a = (q.1 - p.1).atan2(q.0 - p.0);
                let (cp, cq) = (t.c[i], t.c[(i + 1) % 3]);
                let ca = (cq.1 - cp.1).atan2(cq.0 - cp.0);
                if same(a, d) { return Some((cv, norm_ang(ca))); }
                if same(a + pi, d) { return Some((cv, norm_ang(ca + pi))); }
            }
        }
        None
    }
    fn corners_at(&self, v: P, out: &mut Vec<(P, f64, f64, Mk)>) {
        let pi = std::f64::consts::PI; let two = 2.0 * pi;
        let mut iv: Vec<(f64, f64, Mk)> = Vec::new();
        for i in 0..self.tgt.len() {
            let (p, q) = (self.tgt[i], self.tgt[(i + 1) % self.tgt.len()]);
            let o = orient(p, q, v) / norm(sub(q, p));
            if o < -EPS { return; }
            if o.abs() <= EPS { iv.push((norm_ang((q.1 - p.1).atan2(q.0 - p.0) + pi), pi, Mk::ZERO)); }
        }
        for (ti, t) in self.placed.iter().enumerate() {
            let mut inside = true; let mut onedge: Option<usize> = None; let mut vert: Option<usize> = None;
            for i in 0..3 {
                let (p, q) = (t.p[i], t.p[(i + 1) % 3]);
                let o = orient(p, q, v) / norm(sub(q, p));
                if o < -EPS { inside = false; break; }
                if o.abs() <= EPS { onedge = Some(i); }
            }
            if !inside { continue; }
            for i in 0..3 { if norm(sub(t.p[i], v)) <= EPS { vert = Some(i); } }
            let bit = tbit(ti);
            if let Some(k) = vert {
                let a = sub(t.p[(k + 1) % 3], v); let b = sub(t.p[(k + 2) % 3], v);
                iv.push((norm_ang(a.1.atan2(a.0)), cross(a, b).atan2(dot(a, b)), bit));
            } else if let Some(i) = onedge {
                let (p, q) = (t.p[i], t.p[(i + 1) % 3]);
                iv.push((norm_ang((q.1 - p.1).atan2(q.0 - p.0)), pi, bit));
            } else { return; }
        }
        if iv.is_empty() { return; }
        let mut mask = Mk::ZERO; for x in &iv { mask |= x.2; }
        let mut marks: Vec<f64> = Vec::new();
        for &(s, l, _) in &iv { marks.push(s); marks.push(norm_ang(s + l)); }
        marks.sort_by(|a, b| a.partial_cmp(b).unwrap());
        let mut u: Vec<f64> = Vec::new();
        for m in marks { if u.is_empty() || (m - *u.last().unwrap()).abs() > 1e-6 { u.push(m); } }
        if u.len() > 1 && (u[0] + two - *u.last().unwrap()).abs() < 1e-6 { u.pop(); }
        let k = u.len();
        let covered = |a: f64| iv.iter().any(|&(s, l, _)| { let d = norm_ang(a - s); d > 1e-7 && d < l - 1e-7 });
        let mut free = Vec::with_capacity(k); let mut lens = Vec::with_capacity(k);
        for i in 0..k {
            let a = u[i]; let b = if i + 1 < k { u[i + 1] } else { u[0] + two };
            lens.push(b - a); free.push(!covered(norm_ang((a + b) / 2.0)));
        }
        if free.iter().all(|&f| f) { return; }
        let start = (0..k).find(|&i| !free[i]).unwrap();
        let mut arcs: Vec<(f64, f64)> = Vec::new();
        let mut i = 0;
        while i < k {
            let idx = (start + i) % k;
            if free[idx] {
                let d = u[idx]; let mut phi = 0.0; let mut j = i;
                while j < k && free[(start + j) % k] { phi += lens[(start + j) % k]; j += 1; }
                arcs.push((d, phi));
                i = j;
            } else { i += 1; }
        }
        // a branch (v, d) is admissible iff ALL free arcs at v lie in a pointed cone starting at d
        for &(d, phi) in &arcs {
            let ext = arcs.iter().map(|&(dj, pj)| norm_ang(dj - d + 1e-9) - 1e-9 + pj).fold(0.0, f64::max);
            if ext < pi - 1e-6 { out.push((v, d, phi, mask)); }
        }
    }
    /// save the state: new keys and nogoods (and, in tree mode, the new nodes of their trees and of the finished
    /// children on the DFS path), then the frames.  Order: logs first (fsync), then the path file (atomic rename).
    fn checkpoint(&mut self) {
        let ck = match &self.ck { Some(c) => c.clone(), None => return };
        let mut nodes = String::new(); let mut ngs = String::new();
        for i in self.ck_keys_saved..self.kkeys.len() { let k = self.kkeys[i]; ngs.push_str(&format!("k {} {} {} {} {} {}\n", k[0], k[1], k[2], k[3], k[4], k[5])); }
        // keys first: every nogood below refers to key ids that are already in the log
        let mut next = self.next_sid;
        for id in self.ck_ng_saved..self.nogoods.len() {
            let sid = if self.notree { 0 } else { save_tree(&self.ngtree[id], &mut next, &mut nodes) };
            ngs.push_str(&format!("g {} {}", sid, self.nogoods[id].len()));
            for k in &self.nogoods[id] { ngs.push_str(&format!(" {}", k)); }
            ngs.push('\n');
        }
        let mut fr = String::new();
        for f in &self.frames {
            fr.push_str(&format!("f {:016x} {:016x} {:016x} {} {}", f.v.0.to_bits(), f.v.1.to_bits(), f.d.to_bits(), f.nfeas, f.done.len()));
            for (slot, s, mm, tr) in &f.done {
                let sid = if self.notree { 0 } else { save_tree(tr, &mut next, &mut nodes) };
                fr.push_str(&format!(" {} {} {} {}", slot, s, mm.hex(), sid));
            }
            fr.push('\n');
        }
        self.next_sid = next;
        let mut dd = String::new();
        for k in self.dead_log.drain(..) { dd.push_str(&format!("{:032x}\n", k)); }
        if !nodes.is_empty() { self.len_nodes += append_sync(&format!("{}.nodes", ck), &nodes); }
        if !ngs.is_empty() { self.len_ng += append_sync(&format!("{}.ng", ck), &ngs); }
        if !dd.is_empty() { self.len_dead += append_sync(&format!("{}.dead", ck), &dd); }
        self.ck_keys_saved = self.kkeys.len(); self.ck_ng_saved = self.nogoods.len();
        self.ck_count += 1;
        let head = format!("mrv2ck 2\nsig {}\ncounters {} {} {} {} {} {} {}\nlens {} {} {} {}\ntree {}\nframes {}\n{}end\n",
            self.sig, self.calls, self.jumps, self.ng_hits, self.rg_hits, self.secs(), self.maxdepth, self.ck_count,
            self.len_nodes, self.len_ng, self.len_dead, self.next_sid, if self.notree { 0 } else { 1 }, self.frames.len(), fr);
        let tmp = format!("{}.path.tmp", ck);
        { use std::io::Write; let mut f = std::fs::File::create(&tmp).unwrap(); f.write_all(head.as_bytes()).unwrap(); f.sync_all().unwrap(); }
        std::fs::rename(&tmp, format!("{}.path", ck)).unwrap();
    }
    /// load a checkpoint written by `checkpoint`; returns false if there is none
    fn load_ck(&mut self) -> bool {
        let ck = match &self.ck { Some(c) => c.clone(), None => return false };
        let txt = match std::fs::read_to_string(format!("{}.path", ck)) { Ok(t) => t, Err(_) => return false };
        let lines: Vec<&str> = txt.lines().collect();
        if lines.len() < 7 || lines[0] != "mrv2ck 2" || *lines.last().unwrap() != "end" { eprintln!("checkpoint {}.path is not complete: ignored", ck); return false; }
        if lines[1] != format!("sig {}", self.sig) { eprintln!("checkpoint {}.path belongs to another run ({} vs sig {}): delete it to restart", ck, lines[1], self.sig); std::process::exit(3); }
        let c: Vec<u64> = lines[2].split_whitespace().skip(1).map(|x| x.parse().unwrap()).collect();
        let l: Vec<u64> = lines[3].split_whitespace().skip(1).map(|x| x.parse().unwrap()).collect();
        let had_tree = lines[4] == "tree 1";
        if !had_tree && !self.notree { eprintln!("checkpoint {}.path was written without trees (MRV_NOTREE): it can only be resumed with MRV_NOTREE=1", ck); std::process::exit(3); }
        self.calls = c[0]; self.jumps = c[1]; self.ng_hits = c[2]; self.rg_hits = c[3]; self.secs_prev = c[4]; self.maxdepth = c[5] as usize; self.ck_count = c[6];
        self.len_nodes = l[0]; self.len_ng = l[1]; self.len_dead = l[2]; self.next_sid = l[3];
        // drop whatever was appended after the last complete checkpoint
        truncate_to(&format!("{}.nodes", ck), self.len_nodes); truncate_to(&format!("{}.ng", ck), self.len_ng); truncate_to(&format!("{}.dead", ck), self.len_dead);
        let dummy = mk((0.0, 0.0), 0.0, vec![]);
        let mut nodes: Vec<Rc<T>> = vec![dummy.clone()]; // index = log id (ids start at 1)
        if !self.notree {
            let ntxt = std::fs::read_to_string(format!("{}.nodes", ck)).unwrap_or_default();
            for line in ntxt.lines() {
                let w: Vec<&str> = line.split_whitespace().collect();
                let fb = |x: &str| f64::from_bits(u64::from_str_radix(x, 16).unwrap());
                let stub: i64 = w[3].parse().unwrap(); let def: i64 = w[4].parse().unwrap(); let k: usize = w[5].parse().unwrap();
                let mut kids = Vec::with_capacity(k);
                for j in 0..k { let slot: usize = w[6 + 2 * j].parse().unwrap(); let c: usize = w[7 + 2 * j].parse().unwrap(); kids.push((slot, nodes[c].clone())); }
                let id = nodes.len() as u64;
                nodes.push(Rc::new(T { v: (fb(w[0]), fb(w[1])), d: fb(w[2]), kids, stub: if stub < 0 { None } else { Some(stub as usize) }, def: Cell::new(if def < 0 { None } else { Some(def as usize) }), sid: Cell::new(id) }));
            }
            if nodes.len() as u64 != self.next_sid + 1 { eprintln!("checkpoint {}: node log has {} nodes, expected {}", ck, nodes.len() - 1, self.next_sid); std::process::exit(3); }
        } else { self.next_sid = 0; self.len_nodes = 0; let _ = std::fs::remove_file(format!("{}.nodes", ck)); }
        let gtxt = std::fs::read_to_string(format!("{}.ng", ck)).unwrap_or_default();
        for line in gtxt.lines() {
            let mut w = line.split_whitespace();
            match w.next() {
                Some("k") => { let v: Vec<i64> = w.map(|x| x.parse().unwrap()).collect(); let k: Key = [v[0], v[1], v[2], v[3], v[4], v[5]]; let i = self.kkeys.len() as u32; self.kkeys.push(k); self.kid.insert(k, i); }
                Some("g") => {
                    let sid: usize = w.next().unwrap().parse().unwrap(); let _n: usize = w.next().unwrap().parse().unwrap();
                    let ks: Vec<u32> = w.map(|x| x.parse().unwrap()).collect();
                    let id = self.nogoods.len();
                    for k in &ks { self.ngidx.entry(*k).or_default().push(id); }
                    self.ngseen.insert(hash128(&ks));
                    self.nogoods.push(ks);
                    self.ngtree.push(if self.notree { dummy.clone() } else { nodes[sid].clone() });
                }
                _ => {}
            }
        }
        self.ck_keys_saved = self.kkeys.len(); self.ck_ng_saved = self.nogoods.len();
        if let Ok(dtxt) = std::fs::read_to_string(format!("{}.dead", ck)) { for line in dtxt.lines() { if let Ok(k) = u128::from_str_radix(line.trim(), 16) { self.dead.insert(k); } } }
        let nf: usize = lines[5].split_whitespace().nth(1).unwrap().parse().unwrap();
        let mut frames = Vec::new();
        for i in 0..nf {
            let w: Vec<&str> = lines[6 + i].split_whitespace().collect();
            let fb = |x: &str| f64::from_bits(u64::from_str_radix(x, 16).unwrap());
            let nd: usize = w[5].parse().unwrap();
            let mut done = Vec::with_capacity(nd);
            for j in 0..nd {
                let sid: usize = w[9 + 4 * j].parse().unwrap();
                done.push((w[6 + 4 * j].parse().unwrap(), w[7 + 4 * j].parse().unwrap(), Mk::from_hex(w[8 + 4 * j]), if self.notree { dummy.clone() } else { nodes[sid].clone() }));
            }
            frames.push(Frame { v: (fb(w[1]), fb(w[2])), d: fb(w[3]), nfeas: w[4].parse().unwrap(), done });
        }
        frames.reverse();
        self.resume = frames;
        self.last_ck = self.secs_prev;
        eprintln!("resumed from {}.path: secs={} calls={} nogoods={} keys={} nodes={} frames={} dead={}", ck, self.secs_prev, self.calls, self.nogoods.len(), self.kkeys.len(), self.next_sid, nf, self.dead.len());
        true
    }
    /// key of the uncovered region: every free arc (v, d, phi) with phi != pi, at every target/tile vertex
    fn region_key(&self) -> u128 {
        use std::hash::{Hash, Hasher};
        let pi = std::f64::consts::PI; let two = 2.0 * pi;
        let mut pts: Vec<P> = Vec::new();
        let add = |q: P, pts: &mut Vec<P>| { if !pts.iter().any(|&r| norm(sub(r, q)) <= EPS) { pts.push(q); } };
        for i in 0..self.tgt.len() { add(self.tgt[i], &mut pts); }
        for t in &self.placed { for i in 0..3 { add(t.p[i], &mut pts); } }
        let mut ks: Vec<(i64, i64, i64, i64)> = Vec::new();
        'pt: for v in pts {
            let mut iv: Vec<(f64, f64)> = Vec::new();
            for i in 0..self.tgt.len() {
                let (p, q) = (self.tgt[i], self.tgt[(i + 1) % self.tgt.len()]);
                let o = orient(p, q, v) / norm(sub(q, p));
                if o < -EPS { continue 'pt; }
                if o.abs() <= EPS { iv.push((norm_ang((q.1 - p.1).atan2(q.0 - p.0) + pi), pi)); }
            }
            for t in self.placed.iter() {
                let mut inside = true; let mut onedge: Option<usize> = None; let mut vert: Option<usize> = None;
                for i in 0..3 {
                    let (p, q) = (t.p[i], t.p[(i + 1) % 3]);
                    let o = orient(p, q, v) / norm(sub(q, p));
                    if o < -EPS { inside = false; break; }
                    if o.abs() <= EPS { onedge = Some(i); }
                }
                if !inside { continue; }
                for i in 0..3 { if norm(sub(t.p[i], v)) <= EPS { vert = Some(i); } }
                if let Some(k) = vert {
                    let a = sub(t.p[(k + 1) % 3], v); let b = sub(t.p[(k + 2) % 3], v);
                    iv.push((norm_ang(a.1.atan2(a.0)), cross(a, b).atan2(dot(a, b))));
                } else if let Some(i) = onedge {
                    let (p, q) = (t.p[i], t.p[(i + 1) % 3]);
                    iv.push((norm_ang((q.1 - p.1).atan2(q.0 - p.0)), pi));
                } else { continue 'pt; }
            }
            if iv.is_empty() { continue; }
            let mut marks: Vec<f64> = Vec::new();
            for &(s, l) in &iv { marks.push(s); marks.push(norm_ang(s + l)); }
            marks.sort_by(|a, b| a.partial_cmp(b).unwrap());
            let mut u: Vec<f64> = Vec::new();
            for m in marks { if u.is_empty() || (m - *u.last().unwrap()).abs() > 1e-6 { u.push(m); } }
            if u.len() > 1 && (u[0] + two - *u.last().unwrap()).abs() < 1e-6 { u.pop(); }
            let k = u.len();
            let covered = |a: f64| iv.iter().any(|&(s, l)| { let d = norm_ang(a - s); d > 1e-7 && d < l - 1e-7 });
            let mut free = Vec::with_capacity(k); let mut lens = Vec::with_capacity(k);
            for i in 0..k {
                let a = u[i]; let b = if i + 1 < k { u[i + 1] } else { u[0] + two };
                lens.push(b - a); free.push(!covered(norm_ang((a + b) / 2.0)));
            }
            if free.iter().all(|&f| f) { continue; }
            let start = (0..k).find(|&i| !free[i]).unwrap();
            let mut i = 0;
            while i < k {
                let idx = (start + i) % k;
                if free[idx] {
                    let d = u[idx]; let mut phi = 0.0; let mut j = i;
                    while j < k && free[(start + j) % k] { phi += lens[(start + j) % k]; j += 1; }
                    if (phi - pi).abs() > 1e-6 {
                        let dd = norm_ang(d + 5e-7);
                        ks.push(((v.0 * 1e4).round() as i64, (v.1 * 1e4).round() as i64, (dd * 1e5).floor() as i64, (phi * 1e5).round() as i64));
                    }
                    i = j;
                } else { i += 1; }
            }
        }
        ks.sort();
        let mut h1 = std::collections::hash_map::DefaultHasher::new(); ks.hash(&mut h1);
        let mut h2 = std::collections::hash_map::DefaultHasher::new(); 0x9e3779b97f4a7c15u64.hash(&mut h2); ks.hash(&mut h2);
        ((h1.finish() as u128) << 64) | (h2.finish() as u128)
    }
    fn options(&self) -> Vec<Opt> {
        let mut pts: Vec<P> = Vec::new();
        let add = |q: P, pts: &mut Vec<P>| { if !pts.iter().any(|&r| norm(sub(r, q)) <= EPS) { pts.push(q); } };
        for i in 0..self.tgt.len() { add(self.tgt[i], &mut pts); }
        for t in &self.placed { for i in 0..3 { add(t.p[i], &mut pts); } }
        let mut cs = Vec::new();
        for v in pts { self.corners_at(v, &mut cs); }
        let mut out = Vec::new();
        for (v, d, phi, cmask) in cs {
            let mut feas = Vec::new(); let mut mask = cmask;
            let (a, b, c) = (self.side[0], self.side[1], self.side[2]);
            let six = [(a, c, b), (c, a, b), (a, b, c), (b, a, c), (c, b, a), (b, c, a)];
            // conjugation swaps the sides a and c (the conjugate pair) and fixes b
            let csix = [(c, a, b), (a, c, b), (c, b, a), (b, c, a), (a, b, c), (b, a, c)];
            let frame = if self.conj { self.conj_frame(v, d) } else { None };
            for (slot, &(l1, l2, l3)) in six.iter().enumerate() {
                let psi = ((l1 * l1 + l2 * l2 - l3 * l3) / (2.0 * l1 * l2)).acos();
                if psi > phi + 1e-6 { continue; } // blocked by a tile/edge at v: already in cmask
                let p = (v.0 + l1 * d.cos(), v.1 + l1 * d.sin());
                let q = (v.0 + l2 * (d + psi).cos(), v.1 + l2 * (d + psi).sin());
                let mut t = Tri { p: [v, p, q], c: [v, p, q] };
                if !in_closed(&self.tgt, p) || !in_closed(&self.tgt, q) { continue; }
                if let Some((cv, cd)) = frame {
                    let (m1, m2, m3) = csix[slot];
                    let cpsi = ((m1 * m1 + m2 * m2 - m3 * m3) / (2.0 * m1 * m2)).acos();
                    let cp = (cv.0 + m1 * cd.cos(), cv.1 + m1 * cd.sin());
                    let cq = (cv.0 + m2 * (cd + cpsi).cos(), cv.1 + m2 * (cd + cpsi).sin());
                    t.c = [cv, cp, cq];
                    // the conjugate tile must lie in the target (unconditional kill: depends on no placed tile)
                    if !in_closed(&self.tgt, cp) || !in_closed(&self.tgt, cq) { continue; }
                }
                let mut hit: Option<usize> = None; let mut inmask = false;
                for (ui, u) in self.placed.iter().enumerate() {
                    if overlap(u, &t) || (frame.is_some() && overlap_c(u, &t)) {
                        if !(mask & tbit(ui)).is_zero() { inmask = true; hit = Some(ui); break; }
                        if hit.is_none() { hit = Some(ui); }
                    }
                }
                match hit { Some(ui) => { if !inmask { mask |= tbit(ui); } } None => feas.push((slot, t)) }
            }
            out.push(Opt { v, d, phi, feas, mask });
        }
        match self.mode {
            1 => out.sort_by(|a, b| ((!a.feas.is_empty()) as u8, a.v.1, a.v.0).partial_cmp(&((!b.feas.is_empty()) as u8, b.v.1, b.v.0)).unwrap()),
            2 => {
                let ymin = out.iter().map(|o| o.v.1).fold(f64::MAX, f64::min);
                let band = self.band;
                let key = |o: &Opt| -> (usize, f64) { if o.feas.is_empty() { (0, 0.0) } else if o.v.1 <= ymin + band { (o.feas.len(), o.phi) } else { (o.feas.len() + 1000, o.phi) } };
                out.sort_by(|a, b| key(a).partial_cmp(&key(b)).unwrap());
                if !out.is_empty() && !out[0].feas.is_empty() { out.retain(|o| o.v.1 <= ymin + band); }
            }
            _ => out.sort_by(|a, b| (a.feas.len(), a.phi).partial_cmp(&(b.feas.len(), b.phi)).unwrap()),
        }
        out
    }
    // refutation of the current configuration: (tree size, conflict mask, tree); None if not found within limit
    fn solve(&mut self, limit: u32, main: bool) -> R {
        if self.found { return None; }
        if main { self.calls += 1; if self.calls >= self.cap { return None; }
            if self.placed.len() > self.maxdepth { self.maxdepth = self.placed.len(); }
            if self.calls & 255 == 0 && (self.ck.is_some() || self.tl > 0) {
                let secs = self.secs();
                if self.tl > 0 && secs >= self.tl {
                    self.checkpoint();
                    println!("N={} calls={} verdict=TIMEOUT secs={} nogoods={} hits={} checkpoint={}", self.n, self.calls, secs, self.nogoods.len(), self.ng_hits, self.ck.clone().unwrap_or_default());
                    std::process::exit(0);
                }
                if self.ck.is_some() && secs >= self.last_ck + self.ck_secs { self.checkpoint(); self.last_ck = self.secs(); }
            }
            if self.calls & 255 == 0 { if let Some(path) = &self.progpath {
                let secs = self.secs();
                if secs >= self.last_report + 60 {
                    self.last_report = secs;
                    // fraction of the main tree explored, assuming equal subtrees: sum_k idx_k / prod_{j<=k} n_j
                    let mut est = 0.0f64; let mut w = 1.0f64;
                    for &(i, n) in &self.prog { w /= n as f64; est += i as f64 * w; }
                    let head: Vec<String> = self.prog.iter().take(14).map(|&(i, n)| format!("{}/{}", i, n)).collect();
                    use std::io::Write;
                    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
                        let _ = writeln!(f, "secs={} calls={} depth={} maxdepth={} nogoods={} hits={} dead={} rgh={} est={:.6}% path={}", secs, self.calls, self.placed.len(), self.maxdepth, self.nogoods.len(), self.ng_hits, self.dead.len(), self.rg_hits, est * 100.0, head.join(" "));
                    }
                }
            } }
        }
        // a main call that ends before its branching loop cannot use the frames saved for it and its descendants
        let pending = main && !self.resume.is_empty();
        let opts = self.options();
        if opts.is_empty() {
            if self.placed.len() == self.n && main { self.found = true; self.found_tiles = self.placed.clone(); }
            if pending { self.resume.clear(); }
            return None;
        }
        let depth = self.placed.len();
        let bit = tbit(depth);
        // the tile placed at this node is removed from the conflict sets of its children; from depth 128 on its bit is shared and stays
        let clr: Mk = if depth <= MBITS - 1 { !bit } else { Mk::ONES };
        let rkey = if self.region && main { Some(self.region_key()) } else { None };
        if let Some(k) = rkey { if self.dead.contains(&k) { self.rg_hits += 1; if pending { self.resume.clear(); } return Some((1, Mk::below(depth), mk((0.0, 0.0), 0.0, vec![]))); } }
        if let Some((m, id)) = self.lookup() { self.ng_hits += 1; if pending { self.resume.clear(); } return Some((1, m, Rc::new(T { v: (0.0, 0.0), d: 0.0, kids: vec![], stub: Some(id), def: Cell::new(None), sid: Cell::new(0) }))); }
        if opts[0].feas.is_empty() {
            let best = opts.iter().filter(|o| o.feas.is_empty())
                .min_by_key(|o| (o.mask.count_ones(), o.mask.top())).unwrap();
            if pending { self.resume.clear(); }
            return Some((1, best.mask, mk(best.v, best.d, vec![])));
        }
        if limit == 0 { return None; }
        if !main {
            let mut best: R = None;
            for o in &opts {
                let mut tot = 1u64; let mut m = o.mask; let mut ok = true; let mut kids = Vec::new();
                for (slot, t) in &o.feas {
                    self.push(*t);
                    let r = self.solve(limit - 1, false);
                    self.pop();
                    match r {
                        None => { ok = false; break; }
                        Some((s, mm, tr)) => {
                            if self.cbj && (mm & bit).is_zero() { self.jumps += 1; return Some((s, mm, tr)); }
                            tot += s; m |= mm & clr; if !self.notree { kids.push((*slot, tr)); }
                        }
                    }
                }
                if ok && best.as_ref().map_or(true, |b| tot < b.0) { best = Some((tot, m, mk(o.v, o.d, kids))); }
            }
            if let Some((tot, m, tr)) = &best { let (a, b, c) = (*tot, *m, tr.clone()); self.record(a, b, &c); }
            return best;
        }
        let mut bi = 0usize; let mut bscore = u64::MAX; let mut bests: Vec<R> = Vec::new();
        // resume: the frame saved for this main level fixes the branch and restores its finished children
        let rf: Option<Frame> = self.resume.pop();
        if let Some(fr) = &rf {
            match opts.iter().position(|o| !o.feas.is_empty() && norm(sub(o.v, fr.v)) <= EPS && (o.d - fr.d).abs() < 1e-9 && o.feas.len() as u32 == fr.nfeas) {
                Some(i) => bi = i,
                None => { eprintln!("checkpoint does not match the search at main level {}: delete the checkpoint files to restart", self.frames.len()); std::process::exit(3); }
            }
        } else if self.la > 0 && self.mode != 1 {
            for (i, o) in opts.iter().enumerate() {
                let mut sc = 0u64; let mut ests: Vec<R> = Vec::new();
                for (_, t) in &o.feas {
                    self.push(*t);
                    let r = self.solve(self.la, false);
                    self.pop();
                    if let Some((_, mm, _)) = &r { if self.cbj && (*mm & bit).is_zero() { self.jumps += 1; return r; } }
                    sc += match &r { Some(x) => x.0, None => self.w };
                    ests.push(r);
                    if sc >= bscore { break; }
                }
                if sc < bscore { bscore = sc; bi = i; bests = ests; }
            }
        }
        let mut o = opts[bi].clone();
        if depth == 0 { if let Some(rs) = &self.rootslots { o.feas.retain(|(slot, _)| rs.contains(slot)); } }
        let mut tot = 1u64; let mut m = o.mask; let mut kids = Vec::new();
        let mut frame = Frame { v: o.v, d: o.d, nfeas: o.feas.len() as u32, done: Vec::new() };
        let mut start = 0usize; let resumed = rf.is_some();
        if let Some(r) = rf {
            for (i, (slot, s, mm, tr)) in r.done.iter().enumerate() {
                if o.feas[i].0 != *slot { eprintln!("checkpoint does not match the search (slot) at main level {}", self.frames.len()); std::process::exit(3); }
                tot += *s; m |= *mm & clr; if !self.notree { kids.push((*slot, tr.clone())); }
            }
            start = r.done.len(); frame.done = r.done;
        }
        self.frames.push(frame);
        let mut bests = bests.into_iter();
        let nfeas = o.feas.len() as u32;
        for (idx, (slot, t)) in o.feas.iter().enumerate() {
            let pre = bests.next().flatten();
            if idx < start { continue; }
            let r = if pre.is_some() { pre } else {
                self.push(*t);
                self.prog.push((idx as u32, nfeas));
                let r = self.solve(u32::MAX, true);
                self.prog.pop();
                self.pop();
                r
            };
            if resumed { self.resume.clear(); } // the saved frames below this level were for the child just finished
            match r {
                None => { self.frames.pop(); return None; }
                Some((s, mm, tr)) => {
                    if self.cbj && (mm & bit).is_zero() { self.jumps += 1; self.frames.pop(); if let Some(k) = rkey { self.mark_dead(k); } return Some((s, mm, tr)); }
                    tot += s; m |= mm & clr; if !self.notree { kids.push((*slot, tr.clone())); }
                    if self.ck.is_some() { self.frames.last_mut().unwrap().done.push((*slot, s, mm, tr)); }
                }
            }
        }
        self.frames.pop();
        let tr = mk(o.v, o.d, kids);
        self.record(tot, m, &tr);
        if let Some(k) = rkey { self.mark_dead(k); }
        Some((tot, m, tr))
    }
}
fn main() {
    let a: Vec<String> = env::args().collect();
    let f = |i: usize| a[i].parse::<f64>().unwrap();
    let (ta, tb, tc) = (f(1), f(2), f(3));
    let (ga, gb, gc) = (f(4), f(5), f(6));
    let n: usize = a[7].parse().unwrap();
    let la: u32 = a[8].parse().unwrap();
    let cbj = a[9] == "1";
    let cap: u64 = if a.len() > 10 { a[10].parse().unwrap() } else { u64::MAX };
    let w: u64 = if a.len() > 11 { a[11].parse().unwrap() } else { 1000 };
    let (mode, band) = match a.get(13).map(|x| x.as_str()) { Some("lex") => (1u8, 0.0), Some(m) if m.starts_with("band:") => (2u8, m[5..].parse::<f64>().unwrap()), _ => (0u8, 0.0) };
    let ng = a.get(14).map_or(false, |x| x == "ng");
    let angle = |x: f64, y: f64, z: f64| ((y * y + z * z - x * x) / (2.0 * y * z)).acos();
    let cx = (ga * ga + gc * gc - gb * gb) / (2.0 * ga);
    let cy = (gc * gc - cx * cx).sqrt();
    // convex polygon target; MRV_POLY="x,y;x,y;..." (counter-clockwise) overrides the triangle
    let tgt: Vec<P> = match env::var("MRV_POLY") { Ok(v) => v.split(';').map(|q| { let (x, y) = q.split_once(',').unwrap(); (x.trim().parse().unwrap(), y.trim().parse().unwrap()) }).collect(), Err(_) => vec![(0.0, 0.0), (ga, 0.0), (cx, cy)] };
    let mut s = S { tgt, ang: [angle(ta, tb, tc), angle(tb, tc, ta), angle(tc, ta, tb)], side: [ta, tb, tc], n,
        placed: Vec::new(), calls: 0, cap, found: false, la, w, cbj, jumps: 0, mode, band, conj: env::var("MRV_CONJ").is_ok(), conj_kills: 0, found_tiles: Vec::new(), ng, keys: Vec::new(), kset: HashMap::new(), nogoods: Vec::new(), ngtree: Vec::new(), ngidx: HashMap::new(), ngseen: HashSet::new(), ng_hits: 0,
        kid: HashMap::new(), kkeys: Vec::new(), frames: Vec::new(), resume: Vec::new(), ck: env::var("MRV_CKPT").ok(), ck_secs: env::var("MRV_CKPT_SECS").ok().map(|x| x.parse::<u64>().unwrap()).unwrap_or(120), last_ck: 0, secs_prev: 0,
        tl: env::var("MRV_TL").ok().map(|x| x.parse::<u64>().unwrap()).unwrap_or(0), sig: String::new(),
        ck_ng_saved: 0, ck_keys_saved: 0, dead_log: Vec::new(), next_sid: 0, len_nodes: 0, len_ng: 0, len_dead: 0, ck_count: 0, prog: Vec::new(), t_start: std::time::Instant::now(), last_report: 0, maxdepth: 0, progpath: env::var("MRV_PROGRESS").ok(), rootslots: env::var("MRV_ROOTSLOTS").ok().map(|x| x.split(',').map(|y| y.trim().parse::<usize>().unwrap()).collect()), notree: env::var("MRV_NOTREE").is_ok() || env::var("MRV_REGION").is_ok() || (env::var("MRV_ROOTSLOTS").is_ok() && env::var("MRV_ROOTTREE").is_err()), region: env::var("MRV_REGION").is_ok(), dead: HashSet::new(), rg_hits: 0, ngcap: env::var("MRV_NGCAP").ok().map(|x| x.parse::<usize>().unwrap()).unwrap_or(usize::MAX) };
    // signature of the search: everything that determines the tree (not the output paths, not the time limits)
    s.sig = format!("{}_{}_{}_{}_{}_{}_{}_la{}_cbj{}_cap{}_w{}_{}_{}_poly{}_conj{}_ngcap{}_region{}", a[1], a[2], a[3], a[4], a[5], a[6], a[7], a[8], a[9], cap, w,
        a.get(13).map(|x| x.as_str()).unwrap_or("mrv"), if ng { "ng" } else { "nong" }, env::var("MRV_POLY").unwrap_or_default().replace(' ', ""), s.conj as u8,
        if s.ngcap == usize::MAX { 0 } else { s.ngcap }, s.region as u8);
    if let Some(rs) = &s.rootslots { s.sig.push_str(&format!("_root{:?}", rs).replace(' ', "")); }
    if let Some(ck) = s.ck.clone() {
        // a finished run: print its result line again and stop
        if let Ok(res) = std::fs::read_to_string(format!("{}.result", ck)) { if res.contains(&s.sig) { print!("{}", res.lines().last().unwrap_or("")); println!(); return; } }
        if !s.load_ck() { for e in ["nodes", "ng", "dead", "path"] { let _ = std::fs::remove_file(format!("{}.{}", ck, e)); } }
    }
    let t0 = std::time::Instant::now();
    let r = s.solve(u32::MAX, true);
    let (tree, mask) = r.as_ref().map(|x| (x.0, x.1.count_ones())).unwrap_or((0, 0));
    let mut cert_nodes = 0u64; let mut nrefs = 0usize;
    let inl: u64 = a.get(15).map(|x| x.parse().unwrap()).unwrap_or(3);
    if s.notree { /* no tree kept: verdict only */ } else if let Some(x) = r.as_ref() {
        let mut refs: HashSet<usize> = HashSet::new();
        collect(&x.2, &mut refs, &s.ngtree);
        let mut cnt: HashMap<usize, u32> = HashMap::new();
        count(&x.2, true, &refs, &mut cnt, &s.ngtree);
        // a nogood becomes a separate piece iff it is referenced at least twice and is not tiny
        // every stub-referenced nogood is a separate piece (inlining a nogood tree in a foreign context is not sound for replay)
        let _ = (&cnt, inl, tsize as fn(&T) -> u64);
        let piece: HashSet<usize> = refs.clone();
        let mut o = String::from("M\n");
        cert_nodes += emit(&x.2, true, &refs, &piece, &s.ngtree, &mut o);
        let mut ids: Vec<usize> = piece.iter().cloned().collect(); ids.sort();
        nrefs = ids.len();
        for id in ids {
            o.push_str(&format!("N {} {}\n", id, s.nogoods[id].len()));
            let mut kk: Vec<Key> = s.nogoods[id].iter().map(|&i| s.kkeys[i as usize]).collect(); kk.sort();
            for k in &kk { o.push_str(&format!("{} {} {} {} {} {}\n", k[0] as f64 / 1e4, k[1] as f64 / 1e4, k[2] as f64 / 1e4, k[3] as f64 / 1e4, k[4] as f64 / 1e4, k[5] as f64 / 1e4)); }
            cert_nodes += emit(&s.ngtree[id], true, &refs, &piece, &s.ngtree, &mut o);
        }
        if let Some(path) = a.get(12) { if path != "-" { let tmp = format!("{}.tmp", path); std::fs::write(&tmp, o).unwrap(); std::fs::rename(&tmp, path).unwrap(); } }
    }
    if s.found {
        // dump the tiling found (float coordinates; to be verified exactly elsewhere)
        if let Ok(path) = env::var("MRV_TILING") {
            let mut o = String::new();
            for t in &s.found_tiles { o.push_str(&format!("{:.12} {:.12} {:.12} {:.12} {:.12} {:.12}\n", t.p[0].0, t.p[0].1, t.p[1].0, t.p[1].1, t.p[2].0, t.p[2].1)); }
            std::fs::write(path, o).unwrap();
        }
    }
    if s.region { println!("REGION dead={} rg_hits={} expanded={}", s.dead.len(), s.rg_hits, s.calls - s.rg_hits); }
    let line = format!("({},{},{}) in ({},{},{}) N={} la={} cbj={} W={} TREE={} calls={} jumps={} rootmask={} verdict={} secs={:.1} nogoods={} hits={} CERT={} pieces_ng={}",
        ta, tb, tc, ga, gb, gc, n, la, cbj as u8, w, tree, s.calls, s.jumps, mask,
        if s.found { "FOUND" } else if r.is_some() { "NO_TILING" } else { "CAPPED" }, s.secs_prev as f64 + t0.elapsed().as_secs_f64(), s.nogoods.len(), s.ng_hits, cert_nodes, nrefs);
    println!("{}", line);
    if let Some(ck) = &s.ck {
        // the result first (with the signature), then the checkpoint files go
        let tmp = format!("{}.result.tmp", ck);
        std::fs::write(&tmp, format!("sig {}\n{}\n", s.sig, line)).unwrap();
        std::fs::rename(&tmp, format!("{}.result", ck)).unwrap();
        for e in ["nodes", "ng", "dead", "path"] { let _ = std::fs::remove_file(format!("{}.{}", ck, e)); }
    }
}
