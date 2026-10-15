use crate::geo::*;
use crate::int::Int;
use crate::rat::Q;

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
/// `sp`: split candidates (tile index, edge index, line), tried middle-out from `avail` (indices into `sp`);
/// a line that does not properly split a region does not split its sub-regions either.
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

enum Hint { T { v: (f64, f64), d: (f64, f64), s: [u8; 6] }, S(usize) }
struct MNode { v: P, d: P, g: P, recs: Vec<Rec>, kids: [Option<usize>; 6], size: usize, cut: bool, stub: Option<usize> }
/// a nogood: float keys of its tiles, its refutation tree (hints), and once instantiated its exact tiles and root node
struct Ng { keys: Vec<[f64; 6]>, hints: Vec<Hint>, inst: Option<(Vec<Tri>, usize)> }
struct Rp<'a> { g: &'a Geo, cons: &'a Cons<'a>, sq: f64, ngs: std::collections::BTreeMap<usize, Ng>, nodes: Vec<MNode>, dropped: usize }

fn skip(h: &[Hint], pos: &mut usize) {
    let s = match &h[*pos] { Hint::T { s, .. } => *s, Hint::S(_) => [0u8; 6] }; *pos += 1;
    for i in 0..6 { if s[i] == 1 { skip(h, pos); } }
}
fn tri_key(t: &Tri, sq: f64) -> [f64; 6] {
    let mut v: Vec<(f64, f64)> = t.iter().map(|p| (qf(&p.0), qf(&p.1) * sq)).collect();
    v.sort_by(|a, b| a.partial_cmp(b).unwrap());
    [v[0].0, v[0].1, v[1].0, v[1].1, v[2].0, v[2].1]
}
fn same_tri(a: &Tri, b: &Tri) -> bool { a.iter().all(|p| b.iter().any(|q| p == q)) }
impl<'a> Rp<'a> {
    fn stub(&mut self, id: usize, tiles: &[Tri]) -> usize {
        if self.ngs[&id].inst.is_none() {
            // instantiate: match the float keys against the current exact tiles
            let mut r: Vec<Tri> = Vec::new();
            for k in &self.ngs[&id].keys {
                let m: Vec<&Tri> = tiles.iter().filter(|t| { let kk = tri_key(t, self.sq); (0..6).all(|i| (kk[i] - k[i]).abs() < 1e-3) }).collect();
                assert!(m.len() == 1, "nogood {}: key {:?} matches {} current tiles", id, k, m.len());
                r.push(m[0].clone());
            }
            let hints = std::mem::take(&mut self.ngs.get_mut(&id).unwrap().hints);
            let mut pos = 0; let mut tl = r.clone();
            let root = self.replay(&hints, &mut pos, &mut tl);
            assert!(pos == hints.len(), "nogood {}: trailing hints", id);
            self.ngs.get_mut(&id).unwrap().inst = Some((r, root));
        } else {
            let (r, _) = self.ngs[&id].inst.as_ref().unwrap();
            for t in r { assert!(tiles.iter().any(|u| same_tri(t, u)), "nogood {}: not a subset of the current configuration (exact)", id); }
        }
        let nid = self.nodes.len();
        let z: P = (Q::zero(), Q::zero());
        self.nodes.push(MNode { v: z.clone(), d: z.clone(), g: z, recs: vec![], kids: [None; 6], size: 1, cut: false, stub: Some(id) });
        nid
    }
    fn replay(&mut self, h: &[Hint], pos: &mut usize, tiles: &mut Vec<Tri>) -> usize {
        let (hv, hd, hs) = match &h[*pos] { Hint::S(id) => { *pos += 1; return self.stub(*id, tiles); } Hint::T { v, d, s } => (*v, *d, *s) };
        *pos += 1;
        let (g, cons, sq) = (self.g, self.cons, self.sq);
        let mut cands: Vec<P> = g.t.clone();
        for t in tiles.iter() { cands.extend(t.iter().cloned()); }
        let mut found: Option<(P, P, P)> = None;
        'outer: for c in &cands {
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
                    if ok { found = Some((c.clone(), d, gmax.unwrap())); break 'outer; }
                }
            }
        }
        let (v, d, gg) = found.unwrap_or_else(|| panic!("hint {}: no exact convex corner at ({}, {}) dir ({}, {}) with {} tiles", *pos - 1, hv.0, hv.1, hd.0, hd.1, tiles.len()));
        let recs = cons.classify(&v, &d, tiles);
        let nid = self.nodes.len();
        self.nodes.push(MNode { v, d, g: gg, recs: recs.clone(), kids: [None; 6], size: 1, cut: false, stub: None });
        for i in 0..6 {
            let live = recs[i].kill.is_none();
            match (live, hs[i]) {
                (true, 1) => {
                    tiles.push(recs[i].tri.clone());
                    let c = self.replay(h, pos, tiles);
                    tiles.pop();
                    self.nodes[nid].kids[i] = Some(c);
                }
                (false, 1) => { self.dropped += 1; skip(h, pos); }
                (true, _) => panic!("hint {}: placement {} is live in exact arithmetic but killed in the float tree", nid, i),
                _ => {}
            }
        }
        nid
    }
}

struct Cx<'a> { dn: Int, g: &'a Geo, cons: &'a Cons<'a>, tgt: [Hp; 3], ext: Vec<Lin>, emap: Vec<usize>, pl: Vec<(Int, Int, Int, Int, Int)>, name: String }
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
struct Gen<'a> { cx: &'a Cx<'a>, nodes: &'a [MNode], pieces: Vec<(usize, Vec<Tri>, Vec<[Hp; 3]>)>, bytes_bsp: usize, box_retries: usize, ngpiece: std::collections::HashMap<usize, usize> }
impl<'a> Gen<'a> {
    /// text of node `nid` under configuration `tiles`; cut children become stubs and are queued as pieces
    fn node_text(&mut self, nid: usize, tiles: &mut Vec<Tri>, cfg: &mut Vec<[Hp; 3]>, kids_out: &mut Vec<usize>) -> String {
        let cx = self.cx; let nd = &self.nodes[nid]; let dn = &cx.dn; let g = cx.g;
        if let Some(id) = nd.stub { let p = self.ngpiece[&id]; if !kids_out.contains(&p) { kids_out.push(p); } return "Refl.stubM".to_string(); }
        let v = hom(&nd.v); let d = hom(&nd.d); let gv = hom(&nd.g);
        assert!(&d.0 * &d.0 + dn * &d.1 * &d.1 == &d.2 * &d.2);
        assert!((&d.0 * &gv.1 - &d.1 * &gv.0).is_pos());
        let mut kills: Vec<String> = Vec::new(); let mut children: Vec<String> = Vec::new();
        for (k, r) in nd.recs.iter().enumerate() {
            let tri = cx.place(&v, &d, &cx.pl[k]);
            for j in 0..3 {
                let fp = (Q::new(tri[j].0.clone(), tri[j].2.clone()), Q::new(tri[j].1.clone(), tri[j].2.clone()));
                assert!(fp == r.tri[j], "semantic mirror check failed at node {} placement {}", nid, k);
            }
            match &r.kill {
                None => {
                    kills.push("Kill.child".to_string());
                    let c = nd.kids[k].unwrap();
                    tiles.push(r.tri.clone()); cfg.push(tri.clone());
                    if self.nodes[c].cut {
                        let pid = self.pieces.len();
                        self.pieces.push((c, tiles.clone(), cfg.clone()));
                        kids_out.push(pid);
                        children.push("Refl.stubM".to_string());
                    } else {
                        let s = self.node_text(c, tiles, cfg, kids_out);
                        children.push(s);
                    }
                    tiles.pop(); cfg.pop();
                }
                Some(Kill::Escape(kidx, e)) => {
                    let le = cx.emap[*e];
                    kills.push(format!("Kill.esc {} {}", if *kidx == 2 { "true" } else { "false" }, le));
                    let pt = if *kidx == 2 { &tri[2] } else { &tri[1] };
                    if le < 3 { assert!(det3(&cx.tgt[le], &cx.tgt[(le + 1) % 3], pt).is_neg()); }
                    else { let l = &cx.ext[le - 3]; assert!((&l.0 * &pt.0 + &l.1 * &pt.1 + &l.2 * &pt.2).is_neg()); }
                }
                Some(Kill::Overlap(m, w)) => kills.push(format!("Kill.ovl {} ({})", m, pt_s(&hom(w)))),
            }
        }
        // local cone certificate
        let mut tg: Vec<Lin> = (0..3).map(|i| edge(&cx.tgt, i)).collect();
        tg.extend(cx.ext.iter().cloned());
        let ray_d: Lin = (-(&d.1 * &v.2), &d.0 * &v.2, &d.1 * &v.0 - &d.0 * &v.1);
        let ray_g: Lin = (-(&gv.1 * &v.2), &gv.0 * &v.2, &gv.1 * &v.0 - &gv.0 * &v.1);
        let inc = incident(g, &nd.v, tiles);
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
        // box: below the distance from `v` to every tile/target edge that does not contain `v` (float estimate; the
        // certificate is verified exactly, and the box shrinks further if the estimate was too optimistic)
        let sqd = qf(&Q::from_int(dn.clone())).sqrt();
        let fp = |p: &P| (qf(&p.0), qf(&p.1) * sqd);
        let fv = fp(&nd.v);
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
        if best.is_none() {
            eprintln!("node {} v=({}, {}) d=({}, {}) g=({}, {}) tiles={} incident={:?}", nid, nd.v.0, nd.v.1, nd.d.0, nd.d.1, nd.g.0, nd.g.1, tiles.len(), inc);
            for &m in &inc { eprintln!("  tile {}: {:?}", m, tiles[m].iter().map(|p| format!("({},{})", p.0, p.1)).collect::<Vec<_>>()); }
            eprintln!("  free_dirs: {:?}", cx.cons.free_dirs(&nd.v, tiles).map(|a| a.iter().map(|(s, e)| format!("[({},{})->({},{})]", s.0, s.1, e.0, e.1)).collect::<Vec<_>>()));
        }
        let (en, ed, t1, t2) = best.unwrap_or_else(|| panic!("node {}: no local cone certificate", nid));
        self.bytes_bsp += t1.len() + t2.len();
        // hfree
        let mut tau = Q::new(Int::one(), Int::from_i64(4));
        let tq: Vec<_> = tg.iter().map(|x| quad(dn, &v, &d, x)).collect();
        let mut found: Option<(Int, Int, Vec<usize>)> = None;
        for _ in 0..200 {
            let (tn, td) = (tau.n.clone(), tau.d.clone());
            let mut good = tq.iter().all(|c| ok_pos(c, &tn, &td));
            let mut edges = Vec::new();
            if good { for t in cfg.iter() {
                match (0..3).find(|&i| ok_neg(&quad(dn, &v, &d, &edge(t, i)), &tn, &td)) { None => { good = false; break; } Some(i) => edges.push(i) }
            } }
            if good { found = Some((tn, td, edges)); break; }
            tau = &tau / &Q::int(2);
        }
        let (tn, td, edges) = found.unwrap_or_else(|| panic!("node {}: tau", nid));
        format!("NodeM.mk ({}) ({}) ({}) {} {} ({}) ({}) {} {} [{}] [{}] [{}]", pt_s(&v), pt_s(&d), pt_s(&gv), en, ed, t1, t2, tn, td,
            edges.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(","), kills.join(", "), children.join(", "))
    }
}

pub fn run(name: &str, dn_s: &str, target_s: &str, sides_s: &str, hints_path: &str, outdir: &str, cap: usize, modn: usize) {
    let dn = Int::parse(dn_s).expect("Dn");
    let ppt = |s: &str| -> P { let (a, b) = s.split_once(',').unwrap(); (Q::parse(a.trim()).unwrap(), Q::parse(b.trim()).unwrap()) };
    let target: Vec<P> = target_s.split(';').map(|s| ppt(s)).collect();
    let sides_i: Vec<Int> = sides_s.split_whitespace().map(|s| Int::parse(s).unwrap()).collect();
    let sides_q = [Q::from_int(sides_i[0].clone()), Q::from_int(sides_i[1].clone()), Q::from_int(sides_i[2].clone())];
    let geo = Geo::new(Q::from_int(dn.clone()), target.clone(), sides_q);
    let cons = Cons::new(&geo);
    let sq = (dn_s.parse::<f64>().unwrap()).sqrt();
    let mut main_h: Vec<Hint> = Vec::new();
    let mut ngs: std::collections::BTreeMap<usize, Ng> = std::collections::BTreeMap::new();
    let mut cur: Option<usize> = None; let mut need = 0usize;
    for ln in std::fs::read_to_string(hints_path).unwrap().lines() {
        let f: Vec<&str> = ln.split_whitespace().collect();
        if f.is_empty() { continue; }
        if need > 0 { let mut k = [0f64; 6]; for i in 0..6 { k[i] = f[i].parse().unwrap(); } ngs.get_mut(&cur.unwrap()).unwrap().keys.push(k); need -= 1; continue; }
        let h = match f[0] {
            "M" => { cur = None; continue; }
            "N" => { let id: usize = f[1].parse().unwrap(); need = f[2].parse().unwrap(); ngs.insert(id, Ng { keys: vec![], hints: vec![], inst: None }); cur = Some(id); continue; }
            "S" => Hint::S(f[1].parse().unwrap()),
            _ => {
                let o = if f[0] == "T" { 1 } else { 0 };
                let x = |i: usize| f[o + i].parse::<f64>().unwrap();
                let mut s = [0u8; 6]; for i in 0..6 { s[i] = f[o + 4 + i].parse().unwrap(); }
                Hint::T { v: (x(0), x(1)), d: (x(2), x(3)), s }
            }
        };
        match cur { None => main_h.push(h), Some(id) => ngs.get_mut(&id).unwrap().hints.push(h) }
    }
    let t0 = std::time::Instant::now();
    let nh = main_h.len() + ngs.values().map(|n| n.hints.len()).sum::<usize>();
    let mut rp = Rp { g: &geo, cons: &cons, sq, ngs, nodes: Vec::new(), dropped: 0 };
    // the root node must be node 0: reserve it by replaying the main tree first (nogood trees are replayed on first use)
    let mut pos = 0;
    let root = rp.replay(&main_h, &mut pos, &mut Vec::new());
    assert!(root == 0 && pos == main_h.len());
    let mut nodes = std::mem::take(&mut rp.nodes);
    let ngl: Vec<(usize, Vec<Tri>, usize)> = rp.ngs.iter().filter_map(|(id, n)| n.inst.as_ref().map(|(r, root)| (*id, r.clone(), *root))).collect();
    eprintln!("{}: exact replay ok: {} nodes ({} hints, {} float-only subtrees dropped, {} nogoods used of {}), {:.1}s", name, nodes.len(), nh, rp.dropped, ngl.len(), rp.ngs.len(), t0.elapsed().as_secs_f64());
    // piece decomposition (post-order = reverse pre-order index works since children have larger ids)
    for nid in (0..nodes.len()).rev() {
        let mut kids: Vec<usize> = nodes[nid].kids.iter().flatten().cloned().collect();
        let mut sz = 1 + kids.iter().map(|&c| if nodes[c].cut { 1 } else { nodes[c].size }).sum::<usize>();
        kids.sort_by_key(|&c| std::cmp::Reverse(nodes[c].size));
        for c in kids { if sz <= cap { break; } if !nodes[c].cut && nodes[c].size > 1 { sz -= nodes[c].size - 1; nodes[c].cut = true; } }
        nodes[nid].size = sz;
    }
    // polygon target (n >= 4 vertices, counter-clockwise): the Lean triangle is V0, V0 + 4 (V1 - V0), V0 + 4 (V_{n-1} - V0);
    // the other polygon edges become the extra half-planes `ext`; polygon edge e -> Lean escape index emap[e]
    let npoly = target.len();
    let poly = npoly > 3;
    let (tgt, ext, emap): ([Hp; 3], Vec<Lin>, Vec<usize>) = if !poly { ([hom(&target[0]), hom(&target[1]), hom(&target[2])], vec![], vec![0, 1, 2]) } else {
        let four = Q::int(4);
        let v0 = &target[0];
        let bb: P = (&v0.0 + &(&four * &(&target[1].0 - &v0.0)), &v0.1 + &(&four * &(&target[1].1 - &v0.1)));
        let cc: P = (&v0.0 + &(&four * &(&target[npoly - 1].0 - &v0.0)), &v0.1 + &(&four * &(&target[npoly - 1].1 - &v0.1)));
        for q in target.iter() { assert!(geo.inside(&[v0.clone(), bb.clone(), cc.clone()], q, false), "polygon not inside the Lean triangle"); }
        let mut ext = Vec::new(); let mut emap = vec![0usize; npoly];
        emap[0] = 0; emap[npoly - 1] = 2;
        for e in 1..npoly - 1 { emap[e] = 3 + ext.len(); ext.push(lin_of(&hom(&target[e]), &hom(&target[e + 1]))); }
        ([hom(v0), hom(&bb), hom(&cc)], ext, emap)
    };
    let mut pl = Vec::new();
    let z: P = (Q::zero(), Q::zero()); let e1: P = (Q::one(), Q::zero());
    for (l1, l2, l3) in cons.six.iter() { let (pp, qq, _) = cons.third(&z, &e1, l1, l2, l3); pl.push((l1.n.clone(), pp.n, pp.d, qq.n, qq.d)); }
    let cx = Cx { dn: dn.clone(), g: &geo, cons: &cons, tgt: tgt.clone(), ext: ext.clone(), emap, pl, name: name.to_string() };
    let mut gen = Gen { cx: &cx, nodes: &nodes, pieces: vec![(0, vec![], vec![])], bytes_bsp: 0, box_retries: 0, ngpiece: std::collections::HashMap::new() };
    for (id, r, root) in &ngl {
        gen.ngpiece.insert(*id, gen.pieces.len());
        gen.pieces.push((*root, r.clone(), r.iter().map(|t| [hom(&t[0]), hom(&t[1]), hom(&t[2])]).collect()));
    }
    // generate all pieces (queue grows)
    let mut texts: Vec<(String, Vec<usize>, usize, String)> = Vec::new(); // tree text, child pieces, size, cfg text
    let mut i = 0;
    while i < gen.pieces.len() {
        let (nid, tiles, cfg0) = gen.pieces[i].clone();
        let mut tl = tiles.clone();
        let mut cfg: Vec<[Hp; 3]> = cfg0;
        let cfg_s = format!("[{}]", cfg.iter().map(|t| tri_s(t)).collect::<Vec<_>>().join(", "));
        let mut kids = Vec::new();
        let s = gen.node_text(nid, &mut tl, &mut cfg, &mut kids);
        texts.push((s, kids, nodes[nid].size, cfg_s));
        i += 1;
    }
    let np = texts.len();
    eprintln!("{}: {} pieces, max piece {} nodes, bsp bytes {}, box retries {}, {:.1}s", name, np, texts.iter().map(|t| t.2).max().unwrap(), gen.bytes_bsp, gen.box_retries, t0.elapsed().as_secs_f64());
    // module layout: pieces in reverse creation order (children have larger ids than parents => reverse = children first)
    let mut order: Vec<usize> = Vec::new();
    {   // dependencies first (iterative post-order DFS)
        let mut state = vec![0u8; np];
        for r in 0..np {
            if state[r] != 0 { continue; }
            let mut st: Vec<(usize, usize)> = vec![(r, 0)]; state[r] = 1;
            while let Some((p, i)) = st.pop() {
                if i < texts[p].1.len() {
                    st.push((p, i + 1));
                    let q = texts[p].1[i];
                    assert!(state[q] != 1, "cyclic piece dependency");
                    if state[q] == 0 { state[q] = 1; st.push((q, 0)); }
                } else { state[p] = 2; order.push(p); }
            }
        }
    }
    let ns = format!("Refl.M{}", name);
    let inst = format!("def inst : Inst := ⟨{}, {}, ({}, {}, {}), [{}]⟩", dn, tri_s(&tgt), sides_i[0], sides_i[1], sides_i[2],
        cx.pl.iter().map(|(a, b, c, d, e)| format!("⟨{},{},{},{},{}⟩", a, b, c, d, e)).collect::<Vec<_>>().join(", "));
    std::fs::create_dir_all(outdir).unwrap();
    let lin_s = |x: &Lin| format!("⟨{}, {}, {}⟩", l(&x.0), l(&x.1), l(&x.2));
    let ext_def = if poly { format!("def ext : List Lin := [{}]\n", ext.iter().map(|x| lin_s(x)).collect::<Vec<_>>().join(", ")) } else { String::new() };
    std::fs::write(format!("{}/M{}Inst.lean", outdir, name), format!("import Erdos634.Refl.{}\n\n/-! GENERATED by rust/certgenm. Instance `{}`: Dn = {}, tile sides ({}). -/\n\nnamespace {}\nopen Refl\n{}\n{}theorem inst_ok : inst.ok = true := by decide +kernel\nend {}\n", if poly { "CheckPoly" } else { "CheckN" }, name, dn, sides_s, ns, inst, ext_def, ns)).unwrap();
    let mut mods: Vec<Vec<usize>> = vec![vec![]]; let mut acc = 0;
    for &p in &order { if acc > 0 && acc + texts[p].2 > modn { mods.push(vec![]); acc = 0; } mods.last_mut().unwrap().push(p); acc += texts[p].2; }
    let mut total_bytes = 0;
    for (k, ps) in mods.iter().enumerate() {
        let imp = if k == 0 { format!("import Erdos634.Refl.M{}Inst", name) } else { format!("import Erdos634.Refl.M{}Data{}", name, k - 1) };
        let mut s = format!("{}\n\n/-! GENERATED by rust/certgenm: pieces of the `CheckM` certificate of instance `{}` (module {} of {}). -/\n\nset_option maxRecDepth 100000\nnamespace {}\nopen Refl\n", imp, name, k, mods.len(), ns);
        for &p in ps {
            let (t, kids, sz, cfg) = &texts[p];
            s.push_str(&format!("noncomputable def cfg{} : List Tri := {}\n", p, cfg));
            s.push_str(&format!("noncomputable def kn{} : List (List Tri) := [{}]\n", p, kids.iter().map(|q| format!("cfg{}", q)).collect::<Vec<_>>().join(", ")));
            s.push_str(&format!("noncomputable def tree{} : NodeM := {}  -- {} nodes\n", p, t, sz));
            if poly { s.push_str(&format!("theorem ok{} : checkNodeP inst ext kn{} 4000 cfg{} tree{} = true := by decide +kernel\n", p, p, p, p)); } else { s.push_str(&format!("theorem ok{} : checkNodeN inst kn{} 4000 cfg{} tree{} = true := by decide +kernel\n", p, p, p, p)); }
            s.push_str(&format!("theorem cfgok{} : cfg{}.all Tri.ok = true := by decide +kernel\n", p, p));
        }
        s.push_str(&format!("end {}\n", ns));
        total_bytes += s.len();
        std::fs::write(format!("{}/M{}Data{}.lean", outdir, name, k), s).unwrap();
    }
    // soundness glue
    let x3 = (&sides_q_c(&sides_i, 0) * &sides_q_c(&sides_i, 0) + &sides_q_c(&sides_i, 2) * &sides_q_c(&sides_i, 2) - &sides_q_c(&sides_i, 1) * &sides_q_c(&sides_i, 1)) / &(Q::int(2) * &sides_q_c(&sides_i, 0));
    let y3 = ((&sides_q_c(&sides_i, 2) * &sides_q_c(&sides_i, 2) - &x3 * &x3) / &Q::from_int(dn.clone())).sqrt_exact().expect("model apex");
    let qs = |q: &Q| if q.is_int() { format!("{}", q.n) } else { format!("({}/{})", q.n, q.d) };
    let (t0x, t0y, t1x, t1y, t2x, t2y) = (qs(&target[0].0), qs(&target[0].1), qs(&target[1].0), qs(&target[1].1), qs(&target[2].0), qs(&target[2].1));
    if poly {
        let mut b = format!("import Erdos634.Refl.M{}Data{}\nimport Erdos634.Refl.RegionP\n\n/-! GENERATED by rust/certgenm.  Free-branch-point refutation of the POLYGON instance `{}` (`Refl.checkNodeP`):\n    polygon vertices `{}` (second coordinates in units of √{}), tile sides `({})`; {} nodes in {} pieces.\n    `not_region_dissection`: no `CongruentRegionDissection` (any `N`) has region `inst.tgt ∩ ext` and model congruent to `MODEL`. -/\n\nopen Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord\n\nnamespace {}\nopen Refl\n\n", name, mods.len() - 1, name, target_s, dn, sides_s, nodes.len(), np, ns);
        b.push_str(&format!("theorem hDn : (0:ℝ) < {} := by norm_num\n", dn));
        b.push_str(&format!("theorem MODEL_pos : 0 < ef 0 0 {} 0 {} {} := by unfold ef; norm_num\n", sides_i[0], qs(&x3), qs(&y3)));
        b.push_str(&format!("noncomputable def MODEL : Erdos634.Geometry.Tri := rtri {} hDn 0 0 {} 0 {} {} MODEL_pos\n", dn, sides_i[0], qs(&x3), qs(&y3)));
        b.push_str(&format!("theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = {} ∧ dist (MODEL.pts 1) (MODEL.pts 2) = {} ∧\n    dist (MODEL.pts 0) (MODEL.pts 2) = {} :=\n  model_sides_rp hDn MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n", sides_i[0], sides_i[1], sides_i[2]));
        b.push_str("theorem hMa : dist (MODEL.pts 0) (MODEL.pts 1) = (inst.sides.1 : ℝ) := by simpa [inst] using MODEL_sides.1\ntheorem hMb : dist (MODEL.pts 1) (MODEL.pts 2) = (inst.sides.2.1 : ℝ) := by simpa [inst] using MODEL_sides.2.1\ntheorem hMc : dist (MODEL.pts 0) (MODEL.pts 2) = (inst.sides.2.2 : ℝ) := by simpa [inst] using MODEL_sides.2.2\n");
        b.push_str(&format!("theorem hDnI : ((inst.Dn : ℤ) : ℝ) = {} := by norm_num [inst]\n\n", dn));
        for &p in &order {
            let kids = &texts[p].1;
            let hk = if kids.is_empty() { format!("(by intro c hc; simp [kn{}] at hc)", p) } else {
                format!("(by\n    intro c hc\n    simp only [kn{}, List.mem_cons, List.mem_nil_iff, or_false] at hc\n    rcases hc with {}\n{})", p,
                    kids.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | "),
                    kids.iter().map(|q| format!("    · exact sound{}", q)).collect::<Vec<_>>().join("\n")) };
            let hkok = if kids.is_empty() { format!("(by intro c hc; simp [kn{}] at hc)", p) } else {
                format!("(by\n    intro c hc\n    simp only [kn{}, List.mem_cons, List.mem_nil_iff, or_false] at hc\n    rcases hc with {}\n{})", p,
                    kids.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | "),
                    kids.iter().map(|q| format!("    · exact fun t ht => List.all_eq_true.mp cfgok{} t ht", q)).collect::<Vec<_>>().join("\n")) };
            b.push_str(&format!("theorem sound{} : SoundP {} inst ext MODEL cfg{} :=\n  checkNodeP_sound {} hDn inst ext hDnI MODEL hMa hMb hMc inst_ok kn{} {} {} 4000 cfg{} tree{}\n    (fun t ht => List.all_eq_true.mp cfgok{} t ht) ok{}\n", p, dn, p, dn, p, hk, hkok, p, p, p, p));
        }
        b.push_str(&format!("\ntheorem not_region_dissection {{N : ℕ}} (D : Erdos634.RegionDissection.CongruentRegionDissection N)\n    (hR : D.region = inst.tgt.carr {} ∩ extSet {} ext) (hM : D.model.Congruent MODEL) : False :=\n  sound0 (N := N) D hR hM (by simp [cfg0])\n\nend {}\n#print axioms {}.not_region_dissection\n", dn, dn, ns, ns));
        std::fs::write(format!("{}/M{}Sound.lean", outdir, name), b).unwrap();
        eprintln!("{}: wrote {} data modules (polygon), {} bytes of data, {:.1}s", cx.name, mods.len(), total_bytes, t0.elapsed().as_secs_f64());
        return;
    }
    let mut b = format!("import Erdos634.Refl.M{}Data{}\nimport Erdos634.Refl.SoundN\nimport Erdos634.NormalPosition\n\n/-! GENERATED by rust/certgenm.  Free-branch-point (`CheckM`) refutation of instance `{}`:\n    target `({}, {}), ({}, {}), ({}, {}·√{})`, tile sides `({})`; {} nodes in {} pieces.\n    `not_dissection`: no `CongruentDissection` (any `N`) has target congruent to `TGT` and model congruent to `MODEL`. -/\n\nopen Erdos634.CertNode Erdos634.Geometry Erdos634.CertCoord\n\nnamespace {}\nopen Refl\n\n", name, mods.len() - 1, name, t0x, t0y, t1x, t1y, t2x, t2y, dn, sides_s, nodes.len(), np, ns);
    b.push_str(&format!("theorem hDn : (0:ℝ) < {} := by norm_num\n", dn));
    b.push_str(&format!("theorem TGT_pos : 0 < ef {} {} {} {} {} {} := by unfold ef; norm_num\n", t0x, t0y, t1x, t1y, t2x, t2y));
    b.push_str(&format!("noncomputable def TGT : Erdos634.Geometry.Tri := rtri {} hDn {} {} {} {} {} {} TGT_pos\n", dn, t0x, t0y, t1x, t1y, t2x, t2y));
    b.push_str(&format!("theorem MODEL_pos : 0 < ef 0 0 {} 0 {} {} := by unfold ef; norm_num\n", sides_i[0], qs(&x3), qs(&y3)));
    b.push_str(&format!("noncomputable def MODEL : Erdos634.Geometry.Tri := rtri {} hDn 0 0 {} 0 {} {} MODEL_pos\n", dn, sides_i[0], qs(&x3), qs(&y3)));
    b.push_str(&format!("theorem MODEL_sides : dist (MODEL.pts 0) (MODEL.pts 1) = {} ∧ dist (MODEL.pts 1) (MODEL.pts 2) = {} ∧\n    dist (MODEL.pts 0) (MODEL.pts 2) = {} :=\n  model_sides_rp hDn MODEL_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)\n", sides_i[0], sides_i[1], sides_i[2]));
    b.push_str("theorem tgt_ok : inst.tgt.ok = true := by decide +kernel\n");
    b.push_str(&format!("theorem tgt_carr : inst.tgt.carr {} = TGT.carrier := by\n  obtain ⟨hp, h⟩ := Tri.ok_sem {} hDn inst.tgt tgt_ok\n  rw [h]\n  have e1 : inst.tgt.a.X = {} := by simp [inst, pt, Pt.X]\n  have e2 : inst.tgt.a.Y = {} := by simp [inst, pt, Pt.Y]\n  have e3 : inst.tgt.b.X = {} := by simp [inst, pt, Pt.X]\n  have e4 : inst.tgt.b.Y = {} := by simp [inst, pt, Pt.Y]\n  have e5 : inst.tgt.c.X = {} := by simp [inst, pt, Pt.X]\n  have e6 : inst.tgt.c.Y = {} := by simp [inst, pt, Pt.Y]\n  unfold TGT\n  simp only [e1, e2, e3, e4, e5, e6]\n", dn, dn, t0x, t0y, t1x, t1y, t2x, t2y));
    b.push_str("theorem hMa : dist (MODEL.pts 0) (MODEL.pts 1) = (inst.sides.1 : ℝ) := by simpa [inst] using MODEL_sides.1\ntheorem hMb : dist (MODEL.pts 1) (MODEL.pts 2) = (inst.sides.2.1 : ℝ) := by simpa [inst] using MODEL_sides.2.1\ntheorem hMc : dist (MODEL.pts 0) (MODEL.pts 2) = (inst.sides.2.2 : ℝ) := by simpa [inst] using MODEL_sides.2.2\n");
    b.push_str(&format!("theorem hDnI : ((inst.Dn : ℤ) : ℝ) = {} := by norm_num [inst]\n\n", dn));
    for &p in &order {
        let kids = &texts[p].1;
        let hk = if kids.is_empty() { format!("(by intro c hc; simp [kn{}] at hc)", p) } else {
            format!("(by\n    intro c hc\n    simp only [kn{}, List.mem_cons, List.mem_nil_iff, or_false] at hc\n    rcases hc with {}\n{})", p,
                kids.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | "),
                kids.iter().map(|q| format!("    · exact sound{}", q)).collect::<Vec<_>>().join("\n")) };
        let hkok = if kids.is_empty() { format!("(by intro c hc; simp [kn{}] at hc)", p) } else {
            format!("(by\n    intro c hc\n    simp only [kn{}, List.mem_cons, List.mem_nil_iff, or_false] at hc\n    rcases hc with {}\n{})", p,
                kids.iter().map(|_| "rfl").collect::<Vec<_>>().join(" | "),
                kids.iter().map(|q| format!("    · exact fun t ht => List.all_eq_true.mp cfgok{} t ht", q)).collect::<Vec<_>>().join("\n")) };
        b.push_str(&format!("theorem sound{} : Sound {} inst MODEL cfg{} :=\n  checkNodeN_sound {} hDn inst hDnI MODEL hMa hMb hMc inst_ok kn{} {} {} 4000 cfg{} tree{}\n    (fun t ht => List.all_eq_true.mp cfgok{} t ht) ok{}\n", p, dn, p, dn, p, hk, hkok, p, p, p, p));
    }
    b.push_str(&format!("\ntheorem not_dissection {{N : ℕ}} (D : CongruentDissection N)\n    (hT : D.target.Congruent TGT) (hM : D.model.Congruent MODEL) : False := by\n  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hT\n  exact sound0 (N := N) D' (by rw [hD'T, tgt_carr]) (by rw [hD'M]; exact hM) (by simp [cfg0])\n\nend {}\n#print axioms {}.not_dissection\n", ns, ns));
    std::fs::write(format!("{}/M{}Sound.lean", outdir, name), b).unwrap();
    eprintln!("{}: wrote {} data modules, {} bytes of data ({} bytes/node), {:.1}s", cx.name, mods.len(), total_bytes, total_bytes / nodes.len(), t0.elapsed().as_secs_f64());
}
fn sides_q_c(s: &[Int], i: usize) -> Q { Q::from_int(s[i].clone()) }
