use crate::geo::*;
use crate::int::Int;
use crate::rat::Q;
use std::collections::HashMap;

pub type Hp = (Int, Int, Int);
type Lin = (Int, Int, Int);
type Row = (Int, Int, Int, bool);

fn qf(q: &Q) -> f64 {
    let n: f64 = q.n.to_string().parse().unwrap();
    let d: f64 = q.d.to_string().parse().unwrap();
    n / d
}
pub fn hom(p: &P) -> Hp {
    let w = p.0.d.lcm(&p.1.d);
    let wq = Q::from_int(w.clone());
    let x = &p.0 * &wq;
    let y = &p.1 * &wq;
    assert!(x.is_int() && y.is_int());
    (x.n, y.n, w)
}
fn hom3(t: &Tri) -> [Hp; 3] { [hom(&t[0]), hom(&t[1]), hom(&t[2])] }
fn det3(a: &Hp, b: &Hp, c: &Hp) -> Int {
    &a.0 * (&b.1 * &c.2 - &b.2 * &c.1) - &a.1 * (&b.0 * &c.2 - &b.2 * &c.0) + &a.2 * (&b.0 * &c.1 - &b.1 * &c.0)
}
fn lin_of(a: &Hp, b: &Hp) -> Lin {
    (&a.1 * &b.2 - &a.2 * &b.1, &a.2 * &b.0 - &a.0 * &b.2, &a.0 * &b.1 - &a.1 * &b.0)
}
fn edge(t: &[Hp; 3], i: usize) -> Lin { lin_of(&t[i % 3], &t[(i + 1) % 3]) }
fn neg(l: &Lin) -> Lin { (-&l.0, -&l.1, -&l.2) }
fn zero() -> Int { Int::zero() }

struct Item { c: [Int; 3], strict: bool, m: Vec<Int> }
fn fm_cert(rows: &[Row]) -> Option<Vec<Int>> {
    let n = rows.len();
    let items: Vec<Item> = rows.iter().enumerate().map(|(i, r)| Item {
        c: [r.0.clone(), r.1.clone(), r.2.clone()], strict: r.3,
        m: (0..n).map(|j| if j == i { Int::one() } else { Int::zero() }).collect() }).collect();
    fn elim(cs: Vec<Item>, idx: usize) -> Vec<Item> {
        let (mut lo, mut hi, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for c in cs { if c.c[idx].is_pos() { lo.push(c) } else if c.c[idx].is_neg() { hi.push(c) } else { rest.push(c) } }
        for c1 in &lo { for c2 in &hi {
            let k1 = -&c2.c[idx]; let k2 = c1.c[idx].clone();
            let mut co: Vec<Int> = (0..3).map(|i| &k1 * &c1.c[i] + &k2 * &c2.c[i]).collect();
            let mut m: Vec<Int> = c1.m.iter().zip(c2.m.iter()).map(|(x, y)| &k1 * x + &k2 * y).collect();
            let mut gg = Int::zero();
            for x in co.iter().chain(m.iter()) { gg = gg.gcd(&x.abs()); }
            if gg > Int::one() { co = co.iter().map(|x| x.div_exact(&gg)).collect(); m = m.iter().map(|x| x.div_exact(&gg)).collect(); }
            rest.push(Item { c: [co[0].clone(), co[1].clone(), co[2].clone()], strict: c1.strict || c2.strict, m });
        } }
        rest
    }
    let cs = elim(elim(items, 0), 1);
    for c in cs { if c.c[2].is_neg() || (c.c[2].is_zero() && c.strict) { return Some(c.m); } }
    None
}
fn l(x: &Int) -> String { if x.is_neg() { format!("({})", x) } else { format!("{}", x) } }
fn pt_s(p: &Hp) -> String { format!("pt {} {} {}", l(&p.0), l(&p.1), l(&p.2)) }
fn tri_s(t: &[Hp]) -> String { format!("⟨({}), ({}), ({})⟩", pt_s(&t[0]), pt_s(&t[1]), pt_s(&t[2])) }
fn natl(ms: &[Int]) -> String { format!("[{}]", ms.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(",")) }

/// BSP certificate that `rows` (a convex region) is covered by the tiles `cand` (global index, homogeneous tile).
fn bsp_build(cand: &[(usize, [Hp; 3])], sp: &[(usize, usize, Lin)], avail: &[usize], rows: Vec<Row>, depth: usize) -> Option<String> {
    if let Some(c) = fm_cert(&rows) { return Some(format!("Bsp.inf {}", natl(&c))); }
    for (m, t) in cand {
        let mut certs = Vec::new();
        for i in 0..3 {
            let e = edge(t, i);
            let mut r2 = rows.clone();
            r2.push((-&e.0, -&e.1, -&e.2, true));
            match fm_cert(&r2) { None => break, Some(cc) => certs.push(cc) }
        }
        if certs.len() == 3 { return Some(format!("Bsp.tile {} {} {} {}", m, natl(&certs[0]), natl(&certs[1]), natl(&certs[2]))); }
    }
    if depth > 60 { return None; }
    let mut av: Vec<usize> = avail.to_vec();
    while !av.is_empty() {
        let j = av.len() / 2;
        let (m, i, e) = &sp[av[j]];
        let ne = neg(e);
        let mut r1 = rows.clone(); r1.push((e.0.clone(), e.1.clone(), e.2.clone(), false));
        let mut r2 = rows.clone(); r2.push((ne.0.clone(), ne.1.clone(), ne.2.clone(), true));
        av.remove(j);
        if fm_cert(&r1).is_none() && fm_cert(&r2).is_none() {
            let a = bsp_build(cand, sp, &av, r1, depth + 1)?;
            let b = bsp_build(cand, sp, &av, r2, depth + 1)?;
            return Some(format!("Bsp.split {} {} ({}) ({})", m, i, a, b));
        }
    }
    None
}
fn seg_dist(p: (f64, f64), a: (f64, f64), b: (f64, f64)) -> f64 {
    let (dx, dy) = (b.0 - a.0, b.1 - a.1);
    let l2 = dx * dx + dy * dy;
    let t = if l2 == 0.0 { 0.0 } else { (((p.0 - a.0) * dx + (p.1 - a.1) * dy) / l2).max(0.0).min(1.0) };
    let (qx, qy) = (a.0 + t * dx, a.1 + t * dy);
    ((p.0 - qx).powi(2) + (p.1 - qy).powi(2)).sqrt()
}
fn quad(dn: &Int, v: &Hp, d: &Hp, lin: &Lin) -> (Int, Int, Int) {
    ((&lin.0 * &v.0 + &lin.1 * &v.1 + &lin.2 * &v.2) * &d.2, (&lin.0 * &d.0 + &lin.1 * &d.1) * &v.2, (-(&lin.0 * dn * &d.1) + &lin.1 * &d.0) * &v.2)
}
fn ok_pos(c: &(Int, Int, Int), tn: &Int, td: &Int) -> bool {
    let (c0, c1, c2) = c;
    if c0.is_pos() { return (c0 * td * td + c1.min(&zero()) * tn * td + c2.min(&zero()) * tn * tn).is_pos(); }
    if c0.is_zero() { if c1.is_pos() { return (c1 * td + c2.min(&zero()) * tn).is_pos(); } if c1.is_zero() { return !c2.is_neg(); } }
    false
}
fn ok_neg(c: &(Int, Int, Int), tn: &Int, td: &Int) -> bool {
    let (c0, c1, c2) = c;
    if c0.is_neg() { return (c0 * td * td + c1.max(&zero()) * tn * td + c2.max(&zero()) * tn * tn).is_neg(); }
    if c0.is_zero() { if c1.is_neg() { return (c1 * td + c2.max(&zero()) * tn).is_neg(); } if c1.is_zero() { return c2.is_neg(); } }
    false
}

const NONE: u32 = u32::MAX;
/// a node of the float tree (hints only; no exact data)
struct LN { v: (f64, f64), d: (f64, f64), s: [u8; 6], kids: [u32; 6], stub: u32, size: u32, cut: bool }
enum Hint { T { v: (f64, f64), d: (f64, f64), s: [u8; 6] }, S(usize) }

fn build(h: &[Hint], pos: &mut usize, ar: &mut Vec<LN>) -> u32 {
    let idx = ar.len();
    match &h[*pos] {
        Hint::S(id) => { *pos += 1; ar.push(LN { v: (0.0, 0.0), d: (0.0, 0.0), s: [0; 6], kids: [NONE; 6], stub: *id as u32, size: 1, cut: false }); }
        Hint::T { v, d, s } => {
            *pos += 1;
            ar.push(LN { v: *v, d: *d, s: *s, kids: [NONE; 6], stub: NONE, size: 1, cut: false });
            for i in 0..6 { if s[i] == 1 { let c = build(h, pos, ar); ar[idx].kids[i] = c; } }
        }
    }
    idx as u32
}
fn tri_key(t: &Tri, sq: f64) -> [f64; 6] {
    let mut v: Vec<(f64, f64)> = t.iter().map(|p| (qf(&p.0), qf(&p.1) * sq)).collect();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    [v[0].0, v[0].1, v[1].0, v[1].1, v[2].0, v[2].1]
}

struct Cx<'a> { dn: Int, g: &'a Geo, cons: &'a Cons<'a>, tgt: [Hp; 3], pl: Vec<(Int, Int, Int, Int, Int)> }
impl<'a> Cx<'a> {
    fn place(&self, v: &Hp, d: &Hp, pl: &(Int, Int, Int, Int, Int)) -> [Hp; 3] {
        let (l1, pn, pd, qn, qd) = pl; let dn = &self.dn;
        let pp = (&v.0 * &d.2 + l1 * &d.0 * &v.2, &v.1 * &d.2 + l1 * &d.1 * &v.2, &v.2 * &d.2);
        let qq = (&v.0 * &d.2 * pd * qd + pn * &d.0 * &v.2 * qd - dn * qn * &d.1 * &v.2 * pd,
                  &v.1 * &d.2 * pd * qd + pn * &d.1 * &v.2 * qd + qn * &d.0 * &v.2 * pd, &v.2 * &d.2 * pd * qd);
        [v.clone(), pp, qq]
    }
}
/// tiles of `tiles` whose closure contains `v`
fn incident(g: &Geo, v: &P, tiles: &[Tri]) -> Vec<usize> {
    (0..tiles.len()).filter(|&m| g.inside(&tiles[m], v, false)).collect()
}

/// module writer: data modules (core Lean only) and soundness modules (chunks), written as the pieces are completed
struct Out { name: String, ns: String, outdir: String, dn: String, modn: usize, schunk: usize, mirror: bool,
    k: usize, acc: usize, buf: String, data_bytes: usize, sj: usize, scount: usize, sbuf: String, header: String, target_doc: String }
impl Out {
    fn flush_data(&mut self) {
        if self.buf.is_empty() { return; }
        let imp = if self.k == 0 { format!("import Erdos634.Refl.M{}Inst", self.name) } else { format!("import Erdos634.Refl.M{}Data{}", self.name, self.k - 1) };
        let s = format!("{}\n\n/-! GENERATED by rust/certgenx: pieces of the `CheckN` certificate of instance `{}` (module {}). -/\n\nset_option maxRecDepth 100000\nnamespace {}\nopen Refl\n{}end {}\n", imp, self.name, self.k, self.ns, self.buf, self.ns);
        self.data_bytes += s.len();
        std::fs::write(format!("{}/M{}Data{}.lean", self.outdir, self.name, self.k), s).unwrap();
        self.k += 1; self.acc = 0; self.buf.clear();
    }
    /// writes the current chunk of soundness theorems; it imports the data module that holds the last piece added
    fn flush_sound(&mut self) {
        if self.sbuf.is_empty() && self.sj > 0 { return; }
        let imp = if self.sj == 0 {
            format!("import Erdos634.Refl.M{}Data{}\nimport Erdos634.Refl.SoundN\nimport Erdos634.NormalPosition\n{}", self.name, self.k, if self.mirror { "import Erdos634.Refl.SoundMirror\n" } else { "" })
        } else { format!("import Erdos634.Refl.M{}SoundP{}\nimport Erdos634.Refl.M{}Data{}\n", self.name, self.sj - 1, self.name, self.k) };
        let s = format!("{}\n/-! GENERATED by rust/certgenx.  Soundness of the pieces of the certificate of instance `{}` (part {}).{} -/\n\nopen Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord\n\nnamespace {}\nopen Refl\n\n{}{}end {}\n",
            imp, self.name, self.sj, if self.sj == 0 { format!("\n    {}", self.target_doc) } else { String::new() }, self.ns, if self.sj == 0 { self.header.as_str() } else { "" }, self.sbuf, self.ns);
        std::fs::write(format!("{}/M{}SoundP{}.lean", self.outdir, self.name, self.sj), s).unwrap();
        self.sj += 1; self.scount = 0; self.sbuf.clear();
    }
    fn piece(&mut self, data: &str, sound: &str, size: usize) {
        if self.acc > 0 && self.acc + size > self.modn { self.flush_data(); }
        self.buf.push_str(data); self.acc += size;
        self.sbuf.push_str(sound); self.scount += 1;
        if self.scount >= self.schunk { self.flush_sound(); }
    }
}

struct Gx<'a> { cx: &'a Cx<'a>, ar: &'a [LN], sq: f64, main_root: u32, mirror: bool,
    ng_keys: HashMap<usize, Vec<[f64; 6]>>, ng_root: HashMap<usize, u32>, ng_pid: HashMap<usize, usize>,
    npieces: usize, out: Out, dropped: usize, bytes_bsp: usize, box_retries: usize, nodes_done: usize, ng_used: usize,
    mir_pairs: usize, t0: std::time::Instant }
impl<'a> Gx<'a> {
    /// the exact convex corner `(v, d, g)` of the unfilled region named by the float hint
    fn find_corner(&self, hv: (f64, f64), hd: (f64, f64), tiles: &[Tri], nid: u32) -> (P, P, P) {
        let (g, cons, sq) = (self.cx.g, self.cx.cons, self.sq);
        let mut cands: Vec<P> = g.t.clone();
        for t in tiles.iter() { cands.extend(t.iter().cloned()); }
        for c in &cands {
            if (qf(&c.0) - hv.0).abs() > 1e-6 || (qf(&c.1) * sq - hv.1).abs() > 1e-6 { continue; }
            if let Some(arcs) = cons.free_dirs(c, tiles) {
                for (s, _e) in &arcs {
                    let d = match g.unit(s) { Some(d) => d, None => continue };
                    if !((qf(&d.0) - hd.0).abs() < 1e-6 && (qf(&d.1) * sq - hd.1).abs() < 1e-6) { continue; }
                    // all free arcs must lie in a pointed cone [d, gmax], 0 < cross(d, gmax)
                    let mut gmax: Option<P> = None; let mut ok = true;
                    for (sj, ej) in &arcs {
                        let cs = g.cross(s, sj);
                        if cs.is_neg() || (cs.is_zero() && !g.dot(s, sj).is_pos()) { ok = false; break; }
                        if !g.cross(s, ej).is_pos() { ok = false; break; }
                        if gmax.as_ref().map_or(true, |gm| g.cross(gm, ej).is_pos()) { gmax = Some(ej.clone()); }
                    }
                    if ok { return (c.clone(), d, gmax.unwrap()); }
                }
            }
        }
        panic!("node {}: no exact convex corner at ({}, {}) dir ({}, {}) with {} tiles", nid, hv.0, hv.1, hd.0, hd.1, tiles.len());
    }
    fn kill_text(&self, r: &Rec, tri: &[Hp; 3]) -> String {
        match &r.kill {
            None => "Kill.child".to_string(),
            Some(Kill::Escape(kidx, e)) => {
                let pt = if *kidx == 2 { &tri[2] } else { &tri[1] };
                assert!(*e < 3 && det3(&self.cx.tgt[*e], &self.cx.tgt[(*e + 1) % 3], pt).is_neg());
                format!("Kill.esc {} {}", if *kidx == 2 { "true" } else { "false" }, e)
            }
            Some(Kill::Overlap(m, w)) => format!("Kill.ovl {} ({})", m, pt_s(&hom(w))),
        }
    }
    /// local cone certificate and the free-ray parameters of a node; returns the fields `eN eD (t1) (t2) tauN tauD [fedges]`
    fn local_cert(&mut self, nid: u32, nv: &P, v: &Hp, d: &Hp, gv: &Hp, tiles: &[Tri], cfg: &[[Hp; 3]]) -> String {
        let cx = self.cx; let dn = &cx.dn; let g = cx.g;
        assert!(&d.0 * &d.0 + dn * &d.1 * &d.1 == &d.2 * &d.2);
        assert!((&d.0 * &gv.1 - &d.1 * &gv.0).is_pos());
        let tg: Vec<Lin> = (0..3).map(|i| edge(&cx.tgt, i)).collect();
        let ray_d: Lin = (-(&d.1 * &v.2), &d.0 * &v.2, &d.1 * &v.0 - &d.0 * &v.1);
        let ray_g: Lin = (-(&gv.1 * &v.2), &gv.0 * &v.2, &gv.1 * &v.0 - &gv.0 * &v.1);
        let inc = incident(g, nv, tiles);
        let cand: Vec<(usize, [Hp; 3])> = inc.iter().map(|&m| (m, cfg[m].clone())).collect();
        // split candidates: the edges of the incident tiles through `v`, one per direction, sorted by direction
        let mut sp: Vec<(usize, usize, Lin)> = Vec::new(); let mut keys: Vec<f64> = Vec::new();
        for (m, t) in &cand { for i in 0..3 {
            let e = edge(t, i);
            if !(&e.0 * &v.0 + &e.1 * &v.1 + &e.2 * &v.2).is_zero() { continue; }
            let (fa, fb): (f64, f64) = (e.0.to_string().parse().unwrap_or(0.0), e.1.to_string().parse().unwrap_or(0.0));
            let mut ang = fb.atan2(fa); if ang < 0.0 { ang += std::f64::consts::PI; } if ang >= std::f64::consts::PI - 1e-12 { ang = 0.0; }
            if keys.iter().any(|k| (k - ang).abs() < 1e-11) { continue; }
            keys.push(ang); sp.push((*m, i, e));
        } }
        let mut ord: Vec<usize> = (0..sp.len()).collect();
        ord.sort_by(|x, y| keys[*x].partial_cmp(&keys[*y]).unwrap());
        let sp: Vec<(usize, usize, Lin)> = ord.iter().map(|&i| sp[i].clone()).collect();
        let avail: Vec<usize> = (0..sp.len()).collect();
        // box: below the distance from `v` to every tile/target edge that does not contain `v`
        let sqd = qf(&Q::from_int(dn.clone())).sqrt();
        let fp = |p: &P| (qf(&p.0), qf(&p.1) * sqd);
        let fv = fp(nv);
        let mut rmin = f64::MAX;
        let mut feat = |a: &P, b: &P| { let d0 = seg_dist(fv, fp(a), fp(b)); if d0 > 1e-9 && d0 < rmin { rmin = d0; } };
        for t in tiles.iter() { for i in 0..3 { feat(&t[i], &t[(i + 1) % 3]); } }
        let nt = g.t.len();
        for i in 0..nt { feat(&g.t[i], &g.t[(i + 1) % nt]); }
        let lim = 0.45 * rmin / (1.0 + sqd * sqd).sqrt();
        let mut best: Option<(Int, Int, String, String)> = None;
        let en = Int::one(); let mut ed = Int::from_i64(4);
        { let mut w = 0.25f64; while w > lim { w /= 4.0; ed = &ed * &Int::from_i64(4); } }
        for _ in 0..40 {
            let mut base: Vec<Row> = tg.iter().map(|x| (x.0.clone(), x.1.clone(), x.2.clone(), false)).collect();
            let bx: [Lin; 4] = [(&v.2 * &ed, zero(), &en * &v.2 - &v.0 * &ed), (-(&v.2 * &ed), zero(), &en * &v.2 + &v.0 * &ed),
                                (zero(), &v.2 * &ed, &en * &v.2 - &v.1 * &ed), (zero(), -(&v.2 * &ed), &en * &v.2 + &v.1 * &ed)];
            for b in bx.iter() { base.push((b.0.clone(), b.1.clone(), b.2.clone(), false)); }
            let mut r1 = base.clone(); let nd_ = neg(&ray_d); r1.push((nd_.0, nd_.1, nd_.2, true));
            let mut r2 = base.clone(); r2.push((ray_d.0.clone(), ray_d.1.clone(), ray_d.2.clone(), false)); r2.push((ray_g.0.clone(), ray_g.1.clone(), ray_g.2.clone(), true));
            if let Some(t1) = bsp_build(&cand, &sp, &avail, r1, 0) {
                if let Some(t2) = bsp_build(&cand, &sp, &avail, r2, 0) { best = Some((en.clone(), ed.clone(), t1, t2)); break; }
            }
            self.box_retries += 1;
            ed = &ed * &Int::from_i64(4);
        }
        let (en, ed, t1, t2) = best.unwrap_or_else(|| panic!("node {}: no local cone certificate ({} tiles, incident {:?})", nid, tiles.len(), inc));
        self.bytes_bsp += t1.len() + t2.len();
        // hfree
        let mut tau = Q::new(Int::one(), Int::from_i64(4));
        let tq: Vec<_> = tg.iter().map(|x| quad(dn, v, d, x)).collect();
        let mut found: Option<(Int, Int, Vec<usize>)> = None;
        for _ in 0..200 {
            let (tn, td) = (tau.n.clone(), tau.d.clone());
            let mut good = tq.iter().all(|c| ok_pos(c, &tn, &td));
            let mut edges = Vec::new();
            if good { for t in cfg.iter() {
                match (0..3).find(|&i| ok_neg(&quad(dn, v, d, &edge(t, i)), &tn, &td)) { None => { good = false; break; } Some(i) => edges.push(i) }
            } }
            if good { found = Some((tn, td, edges)); break; }
            tau = &tau / &Q::int(2);
        }
        let (tn, td, edges) = found.unwrap_or_else(|| panic!("node {}: tau", nid));
        format!("{} {} ({}) ({}) {} {} [{}]", en, ed, t1, t2, tn, td, edges.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","))
    }
    /// reference to the nogood `id` from the configuration `tiles`; the nogood is instantiated (and its pieces are
    /// generated) at its first use
    fn stub_ref(&mut self, id: usize, tiles: &[Tri]) -> usize {
        let keys = self.ng_keys[&id].clone();
        let mut r: Vec<Tri> = Vec::new();
        for k in &keys {
            let m: Vec<&Tri> = tiles.iter().filter(|t| { let kk = tri_key(t, self.sq); (0..6).all(|i| (kk[i] - k[i]).abs() < 1e-3) }).collect();
            assert!(m.len() == 1, "nogood {}: key {:?} matches {} current tiles", id, k, m.len());
            r.push(m[0].clone());
        }
        if let Some(p) = self.ng_pid.get(&id) { return *p; }
        let cfg: Vec<[Hp; 3]> = r.iter().map(hom3).collect();
        let root = self.ng_root[&id];
        self.ng_used += 1;
        let pid = self.gen_piece(root, r, cfg);
        self.ng_pid.insert(id, pid);
        pid
    }
    fn mir(&self, p: &P) -> P {
        let t = &self.cx.g.t; let (a, b, c) = (&t[0], &t[1], &t[2]);
        let cr = |u: &P, w: &P| &u.0 * &w.1 - &u.1 * &w.0;
        let sb = |u: &P, w: &P| -> P { (&u.0 - &w.0, &u.1 - &w.1) };
        let (ab, ac, ap) = (sb(b, a), sb(c, a), sb(p, a));
        let e = cr(&ab, &ac);
        let s = &cr(&ap, &ac) / &e;
        let u = &cr(&ab, &ap) / &e;
        (&(&a.0 + &(&s * &ac.0)) + &(&u * &ab.0), &(&a.1 + &(&s * &ac.1)) + &(&u * &ab.1))
    }
    fn sound_check(&self, pid: usize, kids: &[usize]) -> String {
        let dn = &self.out.dn;
        let hk = if kids.is_empty() { format!("(by intro c hc; simp [kn{}] at hc)", pid) } else {
            format!("(by\n    intro c hc\n    simp only [kn{}, List.mem_cons, List.mem_nil_iff, or_false] at hc\n    rcases hc with {}\n{})", pid,
                kids.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | "),
                kids.iter().map(|q| format!("    · exact sound{}", q)).collect::<Vec<_>>().join("\n")) };
        let hkok = if kids.is_empty() { format!("(by intro c hc; simp [kn{}] at hc)", pid) } else {
            format!("(by\n    intro c hc\n    simp only [kn{}, List.mem_cons, List.mem_nil_iff, or_false] at hc\n    rcases hc with {}\n{})", pid,
                kids.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | "),
                kids.iter().map(|q| format!("    · exact fun t ht => List.all_eq_true.mp cfgok{} t ht", q)).collect::<Vec<_>>().join("\n")) };
        format!("theorem sound{} : Sound {} inst MODEL cfg{} :=\n  checkNodeN_sound {} hDn inst hDnI MODEL hMa hMb hMc inst_ok kn{} {} {} 4000 cfg{} tree{}\n    (fun t ht => List.all_eq_true.mp cfgok{} t ht) ok{}\n", pid, dn, pid, dn, pid, hk, hkok, pid, pid, pid, pid)
    }
    fn emit_check(&mut self, text: &str, kids: &[usize], size: usize, cfg_s: &str) -> usize {
        let p = self.npieces; self.npieces += 1;
        let mut s = String::new();
        s.push_str(&format!("noncomputable def cfg{} : List Tri := {}\n", p, cfg_s));
        s.push_str(&format!("noncomputable def kn{} : List (List Tri) := [{}]\n", p, kids.iter().map(|q| format!("cfg{}", q)).collect::<Vec<_>>().join(", ")));
        s.push_str(&format!("noncomputable def tree{} : NodeM := {}  -- {} nodes\n", p, text, size));
        s.push_str(&format!("theorem ok{} : checkNodeN inst kn{} 4000 cfg{} tree{} = true := by decide +kernel\n", p, p, p, p));
        s.push_str(&format!("theorem cfgok{} : cfg{}.all Tri.ok = true := by decide +kernel\n", p, p));
        let snd = self.sound_check(p, kids);
        self.out.piece(&s, &snd, size);
        if self.npieces % 2000 == 0 { eprintln!("  {} pieces, {} nodes, {} data modules, {:.0}s", self.npieces, self.nodes_done, self.out.k, self.t0.elapsed().as_secs_f64()); }
        p
    }
    /// a piece: the subtree of `nid` (up to its cut children) under the configuration `tiles`
    fn gen_piece(&mut self, nid: u32, tiles: Vec<Tri>, cfg: Vec<[Hp; 3]>) -> usize {
        let cfg_s = format!("[{}]", cfg.iter().map(|t| tri_s(t)).collect::<Vec<_>>().join(", "));
        let (mut tl, mut cf, mut kids) = (tiles, cfg, Vec::new());
        let text = self.gen_node(nid, &mut tl, &mut cf, &mut kids);
        let size = self.ar[nid as usize].size as usize;
        self.emit_check(&text, &kids, size, &cfg_s)
    }
    /// MIRROR: the one-node refutation of `[tm]` at the root corner; its live placements are explored root placements
    fn gen_bridge(&mut self, hv: (f64, f64), hd: (f64, f64), tm: &Tri, root_pid: &[Option<usize>; 6]) -> usize {
        let tiles = vec![tm.clone()]; let cfg = vec![hom3(tm)];
        let cfg_s = format!("[{}]", tri_s(&cfg[0]));
        let (v, d, gg) = self.find_corner(hv, hd, &tiles, self.main_root);
        let recs = self.cx.cons.classify(&v, &d, &tiles);
        let (hv_, hd_, hg_) = (hom(&v), hom(&d), hom(&gg));
        let (mut kills, mut children, mut kids) = (Vec::new(), Vec::new(), Vec::new());
        for k in 0..6 {
            let tri = self.cx.place(&hv_, &hd_, &self.cx.pl[k]);
            kills.push(self.kill_text(&recs[k], &tri));
            if recs[k].kill.is_none() {
                let p = root_pid[k].unwrap_or_else(|| panic!("mirror: root placement {} is live beside the mirrored tile but has no subtree", k));
                if !kids.contains(&p) { kids.push(p); }
                children.push("Refl.stubM".to_string());
            }
        }
        assert!(!kids.is_empty() || recs.iter().all(|r| r.kill.is_some()));
        let loc = self.local_cert(self.main_root, &v, &hv_, &hd_, &hg_, &tiles, &cfg);
        self.nodes_done += 1;
        let text = format!("NodeM.mk ({}) ({}) ({}) {} [{}] [{}]", pt_s(&hv_), pt_s(&hd_), pt_s(&hg_), loc, kills.join(", "), children.join(", "));
        self.emit_check(&text, &kids, 1, &cfg_s)
    }
    /// MIRROR: the configuration `[t]`, refuted through its mirror image (piece `pb`, configuration `[tm]`)
    fn emit_mirror(&mut self, t: &Tri, tm: &Tri, pb: usize) -> usize {
        let p = self.npieces; self.npieces += 1;
        let (ht, htm) = (hom3(t), hom3(tm));
        let mut s = String::new();
        s.push_str(&format!("noncomputable def cfg{} : List Tri := [{}]\n", p, tri_s(&ht)));
        s.push_str(&format!("theorem cfgok{} : cfg{}.all Tri.ok = true := by decide +kernel\n", p, p));
        let dn = &self.out.dn;
        let snd = format!("theorem sound{} : Sound {} inst MODEL cfg{} :=\n  Refl.sound_mirror {} hDn inst hDnI MODEL tgt_ok mir_iso ({}) ({})\n    (by decide +kernel) (by decide +kernel) (by decide +kernel) sound{}\n", p, dn, p, dn, tri_s(&ht), tri_s(&htm), pb);
        self.out.piece(&s, &snd, 1);
        self.mir_pairs += 1;
        p
    }
    /// text of node `nid` under the configuration `tiles`; cut children become stubs and are generated first
    fn gen_node(&mut self, nid: u32, tiles: &mut Vec<Tri>, cfg: &mut Vec<[Hp; 3]>, kids_out: &mut Vec<usize>) -> String {
        let ar = self.ar; let n = &ar[nid as usize];
        if n.stub != NONE {
            let p = self.stub_ref(n.stub as usize, tiles);
            if !kids_out.contains(&p) { kids_out.push(p); }
            return "Refl.stubM".to_string();
        }
        let (v, d, gg) = self.find_corner(n.v, n.d, tiles, nid);
        let recs = self.cx.cons.classify(&v, &d, tiles);
        let (hv, hd, hg) = (hom(&v), hom(&d), hom(&gg));
        self.nodes_done += 1;
        let mroot = self.mirror && nid == self.main_root && tiles.is_empty();
        let mut kills: Vec<String> = Vec::new();
        let mut child: Vec<Option<String>> = vec![None; 6];
        let mut root_pid: [Option<usize>; 6] = [None; 6];
        let mut missing: Vec<usize> = Vec::new();
        for k in 0..6 {
            let tri = self.cx.place(&hv, &hd, &self.cx.pl[k]);
            for j in 0..3 {
                let fp = (Q::new(tri[j].0.clone(), tri[j].2.clone()), Q::new(tri[j].1.clone(), tri[j].2.clone()));
                assert!(fp == recs[k].tri[j], "semantic mirror check failed at node {} placement {}", nid, k);
            }
            kills.push(self.kill_text(&recs[k], &tri));
            if recs[k].kill.is_some() { if n.s[k] == 1 { self.dropped += 1; } continue; }
            if n.s[k] != 1 {
                if mroot { missing.push(k); continue; }
                panic!("node {}: placement {} is live in exact arithmetic but killed in the float tree", nid, k);
            }
            let c = n.kids[k];
            tiles.push(recs[k].tri.clone()); cfg.push(tri);
            let s = if ar[c as usize].stub == NONE && (ar[c as usize].cut || mroot) {
                let p = self.gen_piece(c, tiles.clone(), cfg.clone());
                kids_out.push(p);
                if mroot { root_pid[k] = Some(p); }
                "Refl.stubM".to_string()
            } else { self.gen_node(c, tiles, cfg, kids_out) };
            tiles.pop(); cfg.pop();
            child[k] = Some(s);
        }
        for &k in &missing {
            let t = recs[k].tri.clone();
            let tm: Tri = [self.mir(&t[0]), self.mir(&t[2]), self.mir(&t[1])];
            let pb = self.gen_bridge(n.v, n.d, &tm, &root_pid);
            let pe = self.emit_mirror(&t, &tm, pb);
            kids_out.push(pe);
            child[k] = Some("Refl.stubM".to_string());
        }
        let loc = self.local_cert(nid, &v, &hv, &hd, &hg, tiles, cfg);
        let children: Vec<String> = child.into_iter().flatten().collect();
        format!("NodeM.mk ({}) ({}) ({}) {} [{}] [{}]", pt_s(&hv), pt_s(&hd), pt_s(&hg), loc, kills.join(", "), children.join(", "))
    }
}

pub fn run(name: &str, dn_s: &str, target_s: &str, sides_s: &str, hints_path: &str, outdir: &str, cap: usize, modn: usize, schunk: usize, mirror: bool) {
    let dn = Int::parse(dn_s).expect("Dn");
    let ppt = |s: &str| -> P { let (a, b) = s.split_once(',').unwrap(); (Q::parse(a.trim()).unwrap(), Q::parse(b.trim()).unwrap()) };
    let target: Vec<P> = target_s.split(';').map(|s| ppt(s)).collect();
    assert!(target.len() == 3, "certgenx: triangle targets only");
    let sides_i: Vec<Int> = sides_s.split_whitespace().map(|s| Int::parse(s).unwrap()).collect();
    let sq_ = |i: usize| Q::from_int(sides_i[i].clone());
    let geo = Geo::new(Q::from_int(dn.clone()), target.clone(), [sq_(0), sq_(1), sq_(2)]);
    let cons = Cons::new(&geo);
    let sq = (dn_s.parse::<f64>().unwrap()).sqrt();
    if mirror {
        let ab = geo.sub(&target[1], &target[0]); let ac = geo.sub(&target[2], &target[0]);
        assert!(geo.norm2(&ab) == geo.norm2(&ac), "mirror mode needs |T0T1| = |T0T2|");
    }
    // hints: main tree and nogood trees
    let t0 = std::time::Instant::now();
    let mut main_h: Vec<Hint> = Vec::new();
    let mut ngh: HashMap<usize, Vec<Hint>> = HashMap::new();
    let mut ng_keys: HashMap<usize, Vec<[f64; 6]>> = HashMap::new();
    let mut order: Vec<usize> = Vec::new();
    let mut cur: Option<usize> = None; let mut need = 0usize;
    for ln in std::fs::read_to_string(hints_path).unwrap().lines() {
        let f: Vec<&str> = ln.split_whitespace().collect();
        if f.is_empty() { continue; }
        if need > 0 { let mut k = [0f64; 6]; for i in 0..6 { k[i] = f[i].parse().unwrap(); } ng_keys.get_mut(&cur.unwrap()).unwrap().push(k); need -= 1; continue; }
        let h = match f[0] {
            "M" => { cur = None; continue; }
            "N" => { let id: usize = f[1].parse().unwrap(); need = f[2].parse().unwrap(); ngh.insert(id, vec![]); ng_keys.insert(id, vec![]); order.push(id); cur = Some(id); continue; }
            "S" => Hint::S(f[1].parse().unwrap()),
            _ => {
                let o = if f[0] == "T" { 1 } else { 0 };
                let x = |i: usize| f[o + i].parse::<f64>().unwrap();
                let mut s = [0u8; 6]; for i in 0..6 { s[i] = f[o + 4 + i].parse().unwrap(); }
                Hint::T { v: (x(0), x(1)), d: (x(2), x(3)), s }
            }
        };
        match cur { None => main_h.push(h), Some(id) => ngh.get_mut(&id).unwrap().push(h) }
    }
    let mut ar: Vec<LN> = Vec::new();
    let mut pos = 0;
    let main_root = build(&main_h, &mut pos, &mut ar);
    assert!(pos == main_h.len(), "main tree: trailing hints");
    drop(main_h);
    let mut ng_root: HashMap<usize, u32> = HashMap::new();
    for id in &order {
        let h = ngh.remove(id).unwrap();
        let mut pos = 0;
        let r = build(&h, &mut pos, &mut ar);
        assert!(pos == h.len(), "nogood {}: trailing hints", id);
        ng_root.insert(*id, r);
    }
    let nh = ar.len();
    // piece decomposition on the float tree (children have larger indices than their parents)
    for nid in (0..ar.len()).rev() {
        if ar[nid].stub != NONE { continue; }
        let mut kids: Vec<usize> = ar[nid].kids.iter().filter(|&&c| c != NONE).map(|&c| c as usize).collect();
        let mut sz = 1 + kids.iter().map(|&c| if ar[c].cut { 1 } else { ar[c].size as usize }).sum::<usize>();
        kids.sort_by_key(|&c| std::cmp::Reverse(ar[c].size));
        for c in kids { if sz <= cap { break; } if !ar[c].cut && ar[c].size > 1 { sz -= ar[c].size as usize - 1; ar[c].cut = true; } }
        ar[nid].size = sz as u32;
    }
    eprintln!("{}: float tree: {} hints ({} nogood trees), {:.1}s", name, nh, order.len(), t0.elapsed().as_secs_f64());
    let tgt: [Hp; 3] = [hom(&target[0]), hom(&target[1]), hom(&target[2])];
    let mut pl = Vec::new();
    let z: P = (Q::zero(), Q::zero()); let e1: P = (Q::one(), Q::zero());
    for (l1, l2, l3) in cons.six.iter() { let (pp, qq, _) = cons.third(&z, &e1, l1, l2, l3); pl.push((l1.n.clone(), pp.n, pp.d, qq.n, qq.d)); }
    let cx = Cx { dn: dn.clone(), g: &geo, cons: &cons, tgt: tgt.clone(), pl };
    let ns = format!("Refl.M{}", name);
    std::fs::create_dir_all(outdir).unwrap();
    let inst = format!("def inst : Inst := ⟨{}, {}, ({}, {}, {}), [{}]⟩", dn, tri_s(&tgt), sides_i[0], sides_i[1], sides_i[2],
        cx.pl.iter().map(|(a, b, c, d, e)| format!("⟨{},{},{},{},{}⟩", a, b, c, d, e)).collect::<Vec<_>>().join(", "));
    std::fs::write(format!("{}/M{}Inst.lean", outdir, name), format!("import Erdos634.Refl.CheckN\n\n/-! GENERATED by rust/certgenx. Instance `{}`: Dn = {}, tile sides ({}). -/\n\nnamespace {}\nopen Refl\n{}\ntheorem inst_ok : inst.ok = true := by decide +kernel\nend {}\n", name, dn, sides_s, ns, inst, ns)).unwrap();
    // header of the soundness glue
    let x3 = (&sq_(0) * &sq_(0) + &sq_(2) * &sq_(2) - &sq_(1) * &sq_(1)) / &(Q::int(2) * &sq_(0));
    let y3 = ((&sq_(2) * &sq_(2) - &x3 * &x3) / &Q::from_int(dn.clone())).sqrt_exact().expect("model apex");
    let qs = |q: &Q| if q.is_int() { format!("{}", q.n) } else { format!("({}/{})", q.n, q.d) };
    let (t0x, t0y, t1x, t1y, t2x, t2y) = (qs(&target[0].0), qs(&target[0].1), qs(&target[1].0), qs(&target[1].1), qs(&target[2].0), qs(&target[2].1));
    let mut b = String::new();
    b.push_str(&format!("theorem hDn : (0:ℝ) < {} := by norm_num\n", dn));
    b.push_str(&format!("theorem TGT_pos : 0 < ef {} {} {} {} {} {} := by unfold ef; norm_num\n", t0x, t0y, t1x, t1y, t2x, t2y));
    b.push_str(&format!("noncomputable def TGT : Erdos634.Geometry.Tri := rtri {} hDn {} {} {} {} {} {} TGT_pos\n", dn, t0x, t0y, t1x, t1y, t2x, t2y));
    b.push_str(&format!("theorem MODEL_pos : 0 < ef 0 0 {} 0 {} {} := by unfold ef; norm_num\n", sides_i[0], qs(&x3), qs(&y3)));
    b.push_str(&format!("noncomputable def MODEL : Erdos634.Geometry.Tri := rtri {} hDn 0 0 {} 0 {} {} MODEL_pos\n", dn, sides_i[0], qs(&x3), qs(&y3)));
    b.push_str(&format!("theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = {} ∧ dist (MODEL.pts 1) (MODEL.pts 2) = {} ∧\n    dist (MODEL.pts 0) (MODEL.pts 2) = {} :=\n  model_sides_rp hDn MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n", sides_i[0], sides_i[1], sides_i[2]));
    b.push_str("theorem tgt_ok : inst.tgt.ok = true := by decide +kernel\n");
    b.push_str(&format!("theorem tgt_carr : inst.tgt.carr {} = TGT.carrier := by\n  obtain ⟨hp, h⟩ := Tri.ok_sem {} hDn inst.tgt tgt_ok\n  rw [h]\n  have e1 : inst.tgt.a.X = {} := by simp [inst, pt, Pt.X]\n  have e2 : inst.tgt.a.Y = {} := by simp [inst, pt, Pt.Y]\n  have e3 : inst.tgt.b.X = {} := by simp [inst, pt, Pt.X]\n  have e4 : inst.tgt.b.Y = {} := by simp [inst, pt, Pt.Y]\n  have e5 : inst.tgt.c.X = {} := by simp [inst, pt, Pt.X]\n  have e6 : inst.tgt.c.Y = {} := by simp [inst, pt, Pt.Y]\n  unfold TGT\n  simp only [e1, e2, e3, e4, e5, e6]\n", dn, dn, t0x, t0y, t1x, t1y, t2x, t2y));
    b.push_str("theorem hMa : dist (MODEL.pts 0) (MODEL.pts 1) = (inst.sides.1 : ℝ) := by simpa [inst] using MODEL_sides.1\ntheorem hMb : dist (MODEL.pts 1) (MODEL.pts 2) = (inst.sides.2.1 : ℝ) := by simpa [inst] using MODEL_sides.2.1\ntheorem hMc : dist (MODEL.pts 0) (MODEL.pts 2) = (inst.sides.2.2 : ℝ) := by simpa [inst] using MODEL_sides.2.2\n");
    b.push_str(&format!("theorem hDnI : ((inst.Dn : ℤ) : ℝ) = {} := by norm_num [inst]\n", dn));
    if mirror { b.push_str("theorem mir_iso : Refl.mirIso inst = true := by decide +kernel\n"); }
    b.push('\n');
    let target_doc = format!("Target `({}, {}), ({}, {}), ({}, {}·√{})`, tile sides `({})`.{}", t0x, t0y, t1x, t1y, t2x, t2y, dn, sides_s,
        if mirror { "  MIRROR mode: root placements without a subtree are refuted through `Refl.sound_mirror`." } else { "" });
    let out = Out { name: name.to_string(), ns: ns.clone(), outdir: outdir.to_string(), dn: dn.to_string(), modn, schunk, mirror,
        k: 0, acc: 0, buf: String::new(), data_bytes: 0, sj: 0, scount: 0, sbuf: String::new(), header: b, target_doc: target_doc.clone() };
    let mut gx = Gx { cx: &cx, ar: &ar, sq, main_root, mirror, ng_keys, ng_root, ng_pid: HashMap::new(), npieces: 0, out,
        dropped: 0, bytes_bsp: 0, box_retries: 0, nodes_done: 0, ng_used: 0, mir_pairs: 0, t0 };
    let root = gx.gen_piece(main_root, vec![], vec![]);
    if mirror { assert!(gx.mir_pairs > 0, "mirror mode, but every live root placement has a subtree"); }
    gx.out.flush_sound();
    gx.out.flush_data();
    let last = gx.out.sj - 1;
    let fin = format!("import Erdos634.Refl.M{}SoundP{}\n\n/-! GENERATED by rust/certgenx.  Free-branch-point (`CheckN`) refutation of instance `{}`:\n    {}\n    {} nodes in {} pieces, {} data modules, {} soundness parts.\n    `not_dissection`: no `CongruentDissection` (any `N`) has target congruent to `TGT` and model congruent to `MODEL`. -/\n\nopen Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord\n\nnamespace {}\nopen Refl\n\ntheorem not_dissection {{N : ℕ}} (D : CongruentDissection N)\n    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False := by\n  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT\n  exact sound{} (N := N) D' (by rw [hD'T, tgt_carr]) (by rw [hD'M]; exact hM) (by simp [cfg{}])\n\nend {}\n#print axioms {}.not_dissection\n",
        name, last, name, target_doc, gx.nodes_done, gx.npieces, gx.out.k, gx.out.sj, ns, root, root, ns, ns);
    std::fs::write(format!("{}/M{}Sound.lean", outdir, name), fin).unwrap();
    eprintln!("{}: exact replay ok: {} nodes ({} hints, {} float-only subtrees dropped, {} nogoods used of {}, {} mirror pairs), {} pieces, bsp bytes {}, box retries {}",
        name, gx.nodes_done, nh, gx.dropped, gx.ng_used, order.len(), gx.mir_pairs, gx.npieces, gx.bytes_bsp, gx.box_retries);
    eprintln!("{}: wrote {} data modules, {} soundness parts, {} bytes of data ({} bytes/node), {:.1}s", name, gx.out.k, gx.out.sj, gx.out.data_bytes, gx.out.data_bytes / gx.nodes_done.max(1), t0.elapsed().as_secs_f64());
}
