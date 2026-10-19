//! Parametric corner-fill template enumerator (Rust port of private/ROOM/ENGINE/template_enum.py, generalised to any rational tile
//! family via angle vectors, plus trapezoid pieces).  Exact arithmetic only.
use crate::aff::*;
use crate::field::*;
use crate::geo::*;
use std::collections::HashSet;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::time::Instant;

#[derive(Clone)]
pub struct Vtx { pub x: Aff, pub y: Aff, pub ang: Ang, pub dir: Ang, pub len: Aff }
#[derive(Clone)]
pub struct Placed { pub kind: u8, pub name: String, pub pts: Vec<(Aff, Aff)>, pub sc: Vec<Aff>, pub flag: bool }
#[derive(Clone)]
pub struct State {
    pub poly: Vec<Vtx>, pub ineq: Vec<Aff>, pub free: Vec<Var>, pub nvar: u16,
    pub pieces: Vec<Placed>, pub hist: Vec<(u16, u8, u16)>, pub elim: Vec<(Var, Aff)>,
    /// pending frontier regions (created by region splits); `poly` is the active one
    pub others: Vec<Vec<Vtx>>,
}

pub struct Shared { pub claimed: std::sync::Mutex<HashSet<u64>>, pub stop: std::sync::atomic::AtomicBool }
pub const SPLIT_DEPTH: usize = 3;

pub struct Slot {
    pub kind: u8, pub name: String, pub ang0: Ang, pub cw: Vec<(Ang, Aff)>, pub along: Aff, pub rel: Vec<(Aff, Aff)>,
    pub sc: Vec<Aff>, pub flag: bool, pub nv: u16, pub pos: Vec<Aff>, pub angy: Ang,
}
impl Slot {
    fn subst(&self, v: Var, f: &Aff) -> Slot {
        Slot { kind: self.kind, name: self.name.clone(), ang0: self.ang0,
            cw: self.cw.iter().map(|(d, l)| (*d, l.subst(v, f))).collect(), along: self.along.subst(v, f),
            rel: self.rel.iter().map(|(x, y)| (x.subst(v, f), y.subst(v, f))).collect(),
            sc: self.sc.iter().map(|a| a.subst(v, f)).collect(), flag: self.flag, nv: self.nv,
            pos: self.pos.iter().map(|a| a.subst(v, f)).collect(), angy: self.angy }
    }
}

#[derive(Clone)]
pub struct Cfg { pub bricks: bool, pub traps: bool, pub k: usize, pub want_all: bool, pub tl: f64, pub maxnodes: u64, pub minp: usize, pub mindim: usize, pub maxbricks: usize, pub eqshape: bool, pub noeqtri: bool, pub nobound: bool, pub sample_depth: usize, pub sample_cap: u64, pub split: bool }

pub struct Enum<'a> {
    pub fam: &'a Fam, pub cfg: Cfg, pub fill: HashSet<Ang>, pub t0: Instant,
    pub nodes: u64, pub lps: u64, pub dead_wedge: u64, pub lp_inf: u64, pub ovf: u64, pub bound_pruned: u64, pub timed_out: bool,
    pub closed: Vec<State>, pub tpoly: Vec<(Aff, Aff)>, pub maxc: usize,
    pub depth_nodes: Vec<u64>, pub filtered: u64, pub sub_start: u64, pub capped: u64,
    pub shared: Option<&'a Shared>, pub ord: u64, pub splits: u64,
}

fn pmul(d: &Dir, l: &Aff) -> (Aff, Aff) { (l.scale(d.c), l.scale(d.s)) }

impl<'a> Enum<'a> {
    pub fn new(fam: &'a Fam, cfg: Cfg) -> Enum<'a> {
        let maxc = if cfg.bricks || cfg.traps || cfg.eqshape { 4 } else { 3 };
        let k = cfg.k;
        Enum { fam, cfg, fill: fam.fill_set(), t0: Instant::now(), nodes: 0, lps: 0, dead_wedge: 0, lp_inf: 0, ovf: 0, bound_pruned: 0,
            timed_out: false, closed: Vec::new(), tpoly: Vec::new(), maxc, depth_nodes: vec![0; k + 2], filtered: 0, sub_start: 0, capped: 0, shared: None, ord: 0, splits: 0 }
    }
    // ---- target ----------------------------------------------------------------------------------------------------------
    /// a triangle target: interior angles, edge lengths (edge i leaves vertex i), direction of edge 0.
    pub fn initial_triangle(&mut self, angs: [Ang; 3], lens: [Aff; 3], d0: Ang, nvar: u16) -> State {
        let f = self.fam; let pi = f.pi();
        let mut dirs = [d0; 3];
        for k in 1..3 { dirs[k] = asub(aadd(dirs[k - 1], pi), angs[k]); }
        let mut pos = (Aff::zero(), Aff::zero());
        let mut poly = Vec::new();
        for k in 0..3 {
            poly.push(Vtx { x: pos.0.clone(), y: pos.1.clone(), ang: angs[k], dir: dirs[k], len: lens[k].clone() });
            let (dx, dy) = pmul(&f.dir(dirs[k]), &lens[k]);
            pos = (pos.0.add(&dx), pos.1.add(&dy));
        }
        assert!(pos.0.is_const() && pos.0.c.is_zero() && pos.1.is_const() && pos.1.c.is_zero() && pos.0.t.is_empty() && pos.1.t.is_empty(), "target does not close: {} {}", pos.0.show(), pos.1.show());
        self.tpoly = poly.iter().map(|v| (v.x.clone(), v.y.clone())).collect();
        State { poly, ineq: vec![Aff::var(0)], free: vec![0], nvar, pieces: vec![], hist: vec![], elim: vec![], others: vec![] }
    }
    // ---- slots -----------------------------------------------------------------------------------------------------------
    fn build_slot(&self, d_out: Ang, angs: &[Ang], lens: &[Aff], kind: u8, name: String, sc: Vec<Aff>, flag: bool, nv: u16, pos: Vec<Aff>, extra: Option<Ang>) -> Slot {
        let f = self.fam; let m = angs.len(); let pi = f.pi();
        let mut dirs = vec![d_out; m];
        for k in 1..m { dirs[k] = asub(aadd(dirs[k - 1], pi), angs[k]); }
        let mut rel = vec![(Aff::zero(), Aff::zero())];
        for k in 0..m - 1 {
            let (dx, dy) = pmul(&f.dir(dirs[k]), &lens[k]);
            let p = rel[k].clone(); rel.push((p.0.add(&dx), p.1.add(&dy)));
        }
        let _ = extra;
        let mut cw = Vec::new();
        for e in (1..m).rev() { cw.push((aadd(dirs[e], pi), lens[e].clone())); }
        Slot { kind, name, ang0: angs[0], cw, along: lens[0].clone(), rel, sc, flag, nv, pos, angy: asub(pi, angs[1]) }
    }
    pub fn slots(&self, d_out: Ang, base: u16) -> Vec<Slot> {
        let f = self.fam; let pi = f.pi(); let mut v = Vec::new();
        let s = Aff::var(base);
        // triangles: all 6 orderings (X,Y,Z) = CCW labelled corners
        for perm in [[0usize, 1, 2], [1, 2, 0], [2, 0, 1], [0, 2, 1], [2, 1, 0], [1, 0, 2]] {
            let [x, y, z] = perm;
            let angs = [f.tang[x], f.tang[y], f.tang[z]];
            let lens = [s.scale(f.tile_side(x, y)), s.scale(f.tile_side(y, z)), s.scale(f.tile_side(z, x))];
            v.push(self.build_slot(d_out, &angs, &lens, 0, format!("tri{}{}{}", "ABC".as_bytes()[x] as char, "ABC".as_bytes()[y] as char, "ABC".as_bytes()[z] as char), vec![s.clone()], false, 1, vec![s.clone()], None));
        }
        if self.cfg.bricks {
            let (p, q) = (Aff::var(base), Aff::var(base + 1));
            for t in 0..3usize {
                let (sp, sq) = (f.sides[(t + 1) % 3], f.sides[(t + 2) % 3]);
                for (sx, sy, ord) in [(sp, sq, 0), (sq, sp, 1)] {
                    for th in 0..2 {
                        let ang = if th == 0 { f.tang[t] } else { asub(pi, f.tang[t]) };
                        let angs = [ang, asub(pi, ang), ang, asub(pi, ang)];
                        let (pl, ql) = (p.scale(Q::int(sx)), q.scale(Q::int(sy)));
                        let lens = [pl.clone(), ql.clone(), pl, ql];
                        v.push(self.build_slot(d_out, &angs, &lens, 1, format!("par{}{}{}", t, ord, th), vec![p.clone(), q.clone()], th == 0, 2, vec![p.clone(), q.clone()], None));
                    }
                }
            }
        }
        if self.cfg.eqshape {
            // equilateral-shape pieces (iso/equi families, units of pi/3): eqtri(s) and the 60-60-120-120 trapezoid eqtrap(x, l)
            let (xv, lv) = (Aff::var(base), Aff::var(base + 1));
            let u = [0, 0, 1]; let u2 = [0, 0, 2];
            let angs0 = [u, u, u2, u2];
            let lens0 = [xv.add(&lv), lv.clone(), xv.clone(), lv.clone()];
            for j in 0..4usize {
                let angs: Vec<Ang> = (0..4).map(|k| angs0[(j + k) % 4]).collect();
                let lens: Vec<Aff> = (0..4).map(|k| lens0[(j + k) % 4].clone()).collect();
                v.push(self.build_slot(d_out, &angs, &lens, 3, format!("eqtrap{}", j), vec![xv.clone(), lv.clone()], false, 2, vec![xv.clone(), lv.clone()], None));
            }
            let s1 = Aff::var(base);
            if !self.cfg.noeqtri { v.push(self.build_slot(d_out, &[u, u, u], &[s1.clone(), s1.clone(), s1.clone()], 3, "eqtri".to_string(), vec![s1.clone()], false, 1, vec![s1.clone()], None)); }
        }
        if self.cfg.traps {
            let (s, sp) = (Aff::var(base), Aff::var(base + 1));
            let diff = s.sub(&sp);
            for x in 0..3usize {
                for ch in 0..2 {
                    let (y, z) = if ch == 0 { ((x + 1) % 3, (x + 2) % 3) } else { ((x + 2) % 3, (x + 1) % 3) };
                    // CCW trapezoid P0=Y, P1=Z, P2=Z', P3=Y'
                    let angs0 = [f.tang[y], f.tang[z], asub(pi, f.tang[z]), asub(pi, f.tang[y])];
                    let lens0 = [s.scale(f.tile_side(y, z)), diff.scale(f.tile_side(z, x)), sp.scale(f.tile_side(y, z)), diff.scale(f.tile_side(x, y))];
                    for j in 0..4usize {
                        let angs: Vec<Ang> = (0..4).map(|k| angs0[(j + k) % 4]).collect();
                        let lens: Vec<Aff> = (0..4).map(|k| lens0[(j + k) % 4].clone()).collect();
                        let mut sl = self.build_slot(d_out, &angs, &lens, 2, format!("trap{}{}{}", x, ch, j), vec![s.clone(), sp.clone()], false, 2, vec![sp.clone(), diff.clone()], None);
                        // apex X: from P0(=Y) going to X along (Y->X): rel pos of Y is rel[(4-j)%4]; direction of edge P3->P0 (CCW) reversed.
                        // compute apex = position(Y) + s*|XY| * dir(Y->X) ; dir(Y->X) = direction of CCW edge (Y'->Y) = dirs[idx]
                        // we recompute directions here for the apex
                        let m = 4; let mut dirs = vec![d_out; m];
                        for k in 1..m { dirs[k] = asub(aadd(dirs[k - 1], pi), angs[k]); }
                        let iy = (4 - j) % 4;                          // index of Y (original P0) in the rotated list
                        let eidx = (iy + 3) % 4;                       // rotated edge index of Y'->Y
                        let (dx, dy) = pmul(&f.dir(aadd(dirs[eidx], pi)), &s.scale(f.tile_side(x, y)));
                        let ry = sl.rel[iy].clone();
                        sl.rel.push((ry.0.add(&dx), ry.1.add(&dy)));
                        // store in a canonical order: Y, Z, Z', Y', X  (rotated back) -> kept as is; expansion uses names
                        sl.name = format!("{}|iy{}", sl.name, iy);
                        v.push(sl);
                    }
                }
            }
        }
        v
    }
    // ---- state operations ------------------------------------------------------------------------------------------------
    fn elim_var(&self, s: &mut State, var: Var, rest: &Aff) {
        s.free.retain(|&x| x != var);
        s.elim.push((var, rest.clone()));
        for v in s.poly.iter_mut().chain(s.others.iter_mut().flatten()) { v.x = v.x.subst(var, rest); v.y = v.y.subst(var, rest); v.len = v.len.subst(var, rest); }
        for f in s.ineq.iter_mut() { *f = f.subst(var, rest); }
        for p in s.pieces.iter_mut() { for q in p.pts.iter_mut() { q.0 = q.0.subst(var, rest); q.1 = q.1.subst(var, rest); } for a in p.sc.iter_mut() { *a = a.subst(var, rest); } }
    }
    /// impose form == 0.  Returns None on contradiction, Some(subst) otherwise (subst = (var, rest) if a variable was eliminated)
    fn add_eq(&self, s: &mut State, form: &Aff) -> Option<Option<(Var, Aff)>> {
        if form.is_const() { return if form.c.is_zero() { Some(None) } else { None }; }
        let var = form.max_var().unwrap(); let co = form.coef(var);
        let mut r = form.clone(); r.t.pop();
        let rest = r.scale(co.inv().neg());
        self.elim_var(s, var, &rest);
        Some(Some((var, rest)))
    }
    fn add_pos(&self, s: &mut State, form: &Aff) -> bool {
        if form.is_const() { return form.c.sign() > 0; }
        s.ineq.push(form.clone()); true
    }
    fn feasible(&mut self, s: &State) -> bool {
        self.lps += 1;
        let m = arena_mark();
        let r = match catch_unwind(AssertUnwindSafe(|| lp_feasible(&s.ineq, &s.free, s.nvar as usize, None))) {
            Ok(r) => r.is_some(),
            Err(_) => { self.ovf += 1; true }
        };
        arena_rewind(m);
        r
    }
    fn norm_ang(&self, a: Ang) -> Ang { self.fam.norm_val(a) }
    // ---- cascade ---------------------------------------------------------------------------------------------------------
    fn resolve(&mut self, s: State, out: &mut Vec<State>) {
        let f = self.fam; let n = s.poly.len();
        if n < 3 {
            if s.others.is_empty() { out.push(s); } else { let mut s = s; s.poly = s.others.remove(0); self.resolve(s, out); }
            return;
        }
        let i = match s.poly.iter().position(|v| v.ang == [0, 0, 0]) { Some(i) => i, None => { out.push(s); return; } };
        let ip = (i + n - 1) % n; let i1 = (i + 1) % n;
        let l_in = s.poly[ip].len.clone(); let l_o = s.poly[i].len.clone(); let d_o = s.poly[i].dir;
        // case l < L
        {
            let mut s1 = s.clone();
            if self.add_pos(&mut s1, &l_in.sub(&l_o)) {
                s1.poly[ip].len = l_in.sub(&l_o);
                let ang = self.norm_ang(aadd(s1.poly[i1].ang, f.pi()));
                s1.poly[i1].ang = ang;
                s1.poly.remove(i);
                if self.feasible(&s1) { self.resolve(s1, out); }
            }
        }
        // case l == L
        {
            let mut s2 = s.clone();
            if let Some(_) = self.add_eq(&mut s2, &l_in.sub(&l_o)) {
                let n2 = s2.poly.len();
                if n2 >= 3 {
                    let ang = self.norm_ang(aadd(s2.poly[ip].ang, s2.poly[i1].ang));
                    let (nd, nl) = (s2.poly[i1].dir, s2.poly[i1].len.clone());
                    s2.poly[ip].ang = ang; s2.poly[ip].dir = nd; s2.poly[ip].len = nl;
                    let (a, b) = if i > i1 { (i, i1) } else { (i1, i) };
                    s2.poly.remove(a); s2.poly.remove(b);
                    if self.feasible(&s2) { self.resolve(s2, out); }
                }
            }
        }
        // case l > L : pass-through at a reflex vertex ip
        if f.val(s.poly[ip].ang) > std::f64::consts::PI + 1e-9 {
            let mut s3 = s.clone();
            if self.add_pos(&mut s3, &l_o.sub(&l_in)) {
                let newang = self.norm_ang(asub(s3.poly[ip].ang, f.pi()));
                s3.poly[ip].ang = newang; s3.poly[ip].dir = d_o; s3.poly[ip].len = l_o.sub(&l_in);
                s3.poly.remove(i);
                if self.feasible(&s3) { self.resolve(s3, out); }
            }
        }
    }
    // ---- placement -------------------------------------------------------------------------------------------------------
    fn place(&mut self, s0: &State, i: usize, sl: &Slot, out: &mut Vec<(u8, State)>) {
        let f = self.fam; let n = s0.poly.len();
        let theta = s0.poly[i].ang;
        let mut rem = asub(theta, sl.ang0);
        let rv = f.val(rem);
        if rv < -1e-9 { return; }
        if rv.abs() < 1e-9 { rem = [0, 0, 0]; }
        if rem != [0, 0, 0] && !self.fill.contains(&rem) { self.dead_wedge += 1; return; }
        let l_out = s0.poly[i].len.clone();
        let d_out = s0.poly[i].dir;
        for case in 0..2u8 {
            let mut s1 = s0.clone(); let mut sl1 = None;
            let diff = l_out.sub(&sl.along);
            if case == 0 { if !self.add_pos(&mut s1, &diff) { continue; } }
            else { match self.add_eq(&mut s1, &diff) { None => continue, Some(Some((v, r))) => { sl1 = Some(sl.subst(v, &r)); } Some(None) => {} } }
            let sl = sl1.as_ref().unwrap_or(sl);
            let vx = s1.poly[i].x.clone(); let vy = s1.poly[i].y.clone();
            let pts: Vec<(Aff, Aff)> = sl.rel.iter().map(|(a, b)| (a.add(&vx), b.add(&vy))).collect();
            s1.pieces.push(Placed { kind: sl.kind, name: sl.name.clone(), pts, sc: sl.sc.clone(), flag: sl.flag });
            let mut newv: Vec<Vtx> = Vec::new(); let mut nvl = 0usize; let mut base_idx = i;
            let mut cur = (vx.clone(), vy.clone());
            newv.push(Vtx { x: vx.clone(), y: vy.clone(), ang: rem, dir: sl.cw[0].0, len: sl.cw[0].1.clone() });
            for j in 1..sl.cw.len() {
                let (dx, dy) = pmul(&f.dir(sl.cw[j - 1].0), &sl.cw[j - 1].1);
                cur = (cur.0.add(&dx), cur.1.add(&dy));
                let ang = f.interior(sl.cw[j - 1].0, sl.cw[j].0);
                newv.push(Vtx { x: cur.0.clone(), y: cur.1.clone(), ang: f.norm_val(ang), dir: sl.cw[j].0, len: sl.cw[j].1.clone() });
            }
            let last = sl.cw.last().unwrap();
            let (dx, dy) = pmul(&f.dir(last.0), &last.1);
            let yp = (cur.0.add(&dx), cur.1.add(&dy));
            if case == 0 {
                newv.push(Vtx { x: yp.0, y: yp.1, ang: sl.angy, dir: d_out, len: s1.poly[i].len.sub(&sl.along.clone()) });
                // note: s1.poly[i].len is l_out (possibly substituted) ; along is the slot's (already reduced)
                nvl = newv.len();
                let mut poly: Vec<Vtx> = s1.poly[..i].to_vec(); poly.extend(newv); poly.extend(s1.poly[i + 1..].iter().cloned());
                s1.poly = poly;
            } else {
                let i1 = (i + 1) % n; let old = s1.poly[i1].clone();
                let na = asub(old.ang, asub(f.pi(), sl.angy));
                let nv = f.val(na);
                if nv < -1e-9 { continue; }
                let na = if nv.abs() < 1e-9 { [0, 0, 0] } else { na };
                newv.push(Vtx { x: yp.0, y: yp.1, ang: na, dir: old.dir, len: old.len.clone() });
                nvl = newv.len(); if i1 == 0 { base_idx = i - 1; }
                if i1 == 0 { let mut poly: Vec<Vtx> = s1.poly[1..i].to_vec(); poly.extend(newv); s1.poly = poly; }
                else { let mut poly: Vec<Vtx> = s1.poly[..i].to_vec(); poly.extend(newv); poly.extend(s1.poly[i1 + 1..].iter().cloned()); s1.poly = poly; }
            }
            let mut variants: Vec<State> = Vec::new();
            if self.cfg.split && nvl >= 3 { for m in 0..nvl - 2 { self.split_variants(&s1, base_idx + 1 + m, &mut variants); } }
            let mut res = Vec::new();
            if !self.feasible(&s1) { self.lp_inf += 1; } else { self.resolve(s1, &mut res); }
            for sv in variants { if self.feasible(&sv) { self.splits += 1; self.resolve(sv, &mut res); } }
            for r in res { out.push((case, r)); }
        }
    }
    /// region-split moves: the piece vertex `vi` (a reflex vertex of the new frontier) lies in the open interior of a non-adjacent
    /// frontier edge j.  One linear equation (collinearity) + t in (0, len_j); the frontier splits into two regions that are
    /// tiled independently (they share the parameters).  Vertex-on-vertex coincidences (t = 0 or len) are NOT generated.
    fn split_variants(&mut self, s1: &State, vi: usize, out: &mut Vec<State>) {
        let f = self.fam; let n = s1.poly.len();
        if n < 4 || vi >= n { return; }
        let av = f.val(s1.poly[vi].ang);
        if av <= std::f64::consts::PI + 1e-9 { return; }
        let prev = (vi + n - 1) % n;
        for j in 0..n {
            if j == vi || j == prev { continue; }
            let j1 = (j + 1) % n;
            let r1 = (j + n - vi) % n + 1; let r2 = (prev + n - j1) % n + 2;
            if r1 < 3 || r2 < 3 { continue; }
            let dj = f.dir(s1.poly[j].dir);
            let eq = s1.poly[vi].x.sub(&s1.poly[j].x).scale(dj.s).sub(&s1.poly[vi].y.sub(&s1.poly[j].y).scale(dj.c));
            if eq.is_const() && !eq.c.is_zero() { continue; }
            let a1 = f.norm_val(f.interior(s1.poly[j].dir, s1.poly[vi].dir));
            let a2 = f.norm_val(f.interior(s1.poly[prev].dir, s1.poly[j].dir));
            let (v1, v2) = (f.val(a1), f.val(a2));
            if v1 < -1e-9 || v2 < -1e-9 { continue; }
            if (v1 + v2 - (av - std::f64::consts::PI)).abs() > 1e-7 { continue; }
            let mut s2 = s1.clone();
            if self.add_eq(&mut s2, &eq).is_none() { continue; }
            let dx = s2.poly[vi].x.sub(&s2.poly[j].x); let dy = s2.poly[vi].y.sub(&s2.poly[j].y);
            let t = if !dj.c.is_zero() { dx.scale(dj.c.inv()) } else { dy.scale(dj.s.inv()) };
            let lj = s2.poly[j].len.clone();
            if !self.add_pos(&mut s2, &t) { continue; }
            if !self.add_pos(&mut s2, &lj.sub(&t)) { continue; }
            let mut reg1: Vec<Vtx> = Vec::new(); let mut k = vi;
            loop { reg1.push(s2.poly[k].clone()); if k == j { break; } k = (k + 1) % n; }
            reg1[0].ang = a1; reg1.last_mut().unwrap().len = t.clone();
            let mut reg2: Vec<Vtx> = Vec::new(); k = j1;
            loop { reg2.push(s2.poly[k].clone()); if k == prev { break; } k = (k + 1) % n; }
            let mut vv = s2.poly[vi].clone(); vv.ang = a2; vv.dir = s2.poly[j].dir; vv.len = lj.sub(&t); reg2.push(vv);
            s2.poly = reg1; s2.others.insert(0, reg2);
            out.push(s2);
        }
    }
    // ---- DFS -------------------------------------------------------------------------------------------------------------
    fn corner(&self, s: &State) -> Option<usize> {
        let mut best: Option<(f64, usize)> = None;
        for (j, v) in s.poly.iter().enumerate() {
            let av = self.fam.val(v.ang);
            if av < std::f64::consts::PI - 1e-9 && (best.is_none() || av < best.unwrap().0 - 1e-9) { best = Some((av, j)); }
        }
        best.map(|b| b.1)
    }
    fn weight(&self, s: &State) -> usize {
        let mut w = 0;
        for v in s.poly.iter().chain(s.others.iter().flatten()) { let av = self.fam.val(v.ang); if (av - std::f64::consts::PI).abs() < 1e-9 { continue; } w += if av < std::f64::consts::PI { 1 } else { 2 }; }
        w
    }
    pub fn expand(&mut self, s: &State, depth: usize) -> Vec<(u16, u8, State)> {
        let i = match self.corner(s) { Some(i) => i, None => return vec![] };
        let d_out = s.poly[i].dir;
        let base = s.nvar;
        let slots = self.slots(d_out, base);
        let mut kids = Vec::new();
        let _ = depth;
        let nbr = s.pieces.iter().filter(|p| p.kind != 0).count();
        let corner_ang = s.poly[i].ang;
        let mut keyed: Vec<(u8, u8, usize, State)> = Vec::new();
        for (si, sl) in slots.iter().enumerate() {
            if sl.kind != 0 && nbr >= self.cfg.maxbricks { continue; }
            let mut s0 = s.clone();
            s0.nvar = base + sl.nv;
            for k in 0..sl.nv { s0.free.push(base + k); }
            for p in &sl.pos { s0.ineq.push(p.clone()); }
            let mut out = Vec::new();
            let r = catch_unwind(AssertUnwindSafe(|| { self.place(&s0, i, sl, &mut out); }));
            if r.is_err() { self.ovf += 1; out.clear(); }
            let k0 = if sl.ang0 == corner_ang { 0u8 } else { 1u8 };
            for (case, st) in out { keyed.push((k0, case, si, st)); }
        }
        keyed.sort_by_key(|k| (k.0, 1 - k.1));
        let mut occ: std::collections::HashMap<(usize, u8), u16> = std::collections::HashMap::new();
        for (_, case, si, mut st) in keyed {
            let o = occ.entry((si, case)).or_insert(0); let oc = *o; *o += 1;
            st.hist.push((si as u16, case, oc)); kids.push((si as u16, case, st));
        }
        kids
    }
    pub fn search(&mut self, s: State, depth: usize) -> bool {
        self.nodes += 1; self.depth_nodes[depth.min(self.cfg.k + 1)] += 1;
        if self.nodes % 256 == 0 && (self.t0.elapsed().as_secs_f64() > self.cfg.tl || (self.cfg.maxnodes > 0 && self.nodes > self.cfg.maxnodes)) { self.timed_out = true; }
        if self.timed_out { return false; }
        if let Some(sh) = self.shared {
            if sh.stop.load(std::sync::atomic::Ordering::Relaxed) { return false; }
            if depth == SPLIT_DEPTH { let o = self.ord; self.ord += 1; if !sh.claimed.lock().unwrap().insert(o) { return false; } }
        }
        if self.cfg.sample_depth > 0 {
            if depth == self.cfg.sample_depth { self.sub_start = self.nodes; }
            else if depth > self.cfg.sample_depth && self.nodes - self.sub_start > self.cfg.sample_cap { self.capped += 1; return false; }
        }
        if s.poly.len() < 3 {
            if s.pieces.len() >= self.cfg.minp && s.free.len() >= self.cfg.mindim { self.closed.push(s); arena_pin(); if !self.cfg.want_all { if let Some(sh) = self.shared { sh.stop.store(true, std::sync::atomic::Ordering::Relaxed); } } return !self.cfg.want_all; }
            self.filtered += 1; return false;
        }
        if depth >= self.cfg.k { return false; }
        // dead wedge at every vertex
        for v in s.poly.iter().chain(s.others.iter().flatten()) { if v.ang != [0, 0, 0] && !self.fill.contains(&v.ang) { self.dead_wedge += 1; return false; } }
        let need = (self.weight(&s) + self.maxc - 1) / self.maxc;
        if !self.cfg.nobound && need > self.cfg.k - depth { self.bound_pruned += 1; return false; }
        let kids = match catch_unwind(AssertUnwindSafe(|| self.expand(&s, depth))) { Ok(k) => k, Err(_) => { self.ovf += 1; vec![] } };
        let mk = arena_mark();
        for (_, _, st) in kids {
            if self.search(st, depth + 1) { return true; }
            arena_rewind(mk);
        }
        false
    }
}
