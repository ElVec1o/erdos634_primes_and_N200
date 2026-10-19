#[allow(dead_code)] mod field;
mod aff; mod geo; mod search;
use aff::*; use field::*; use geo::*; use search::*;
use std::collections::HashSet;

static BIGPT: std::sync::atomic::AtomicU64 = std::sync::atomic::AtomicU64::new(0);
fn gcd_i(a: i128, b: i128) -> i128 { gcd(a, b) }
fn lcm_i(a: i128, b: i128) -> i128 { a / gcd_i(a, b) * b }
fn cross(p: &(Q, Q), q: &(Q, Q)) -> Q { p.0.mul(q.1).sub(p.1.mul(q.0)) }
fn subp(p: &(Q, Q), q: &(Q, Q)) -> (Q, Q) { (p.0.sub(q.0), p.1.sub(q.1)) }
fn area2(v: &[(Q, Q)]) -> Q { let mut s = Q::ZERO; for i in 0..v.len() { s = s.add(cross(&v[i], &v[(i + 1) % v.len()])); } s }
fn sep(a: &[(Q, Q)], b: &[(Q, Q)]) -> bool {
    for poly in [a, b] {
        let n = poly.len();
        for i in 0..n {
            let (p, d) = (poly[i], subp(&poly[(i + 1) % n], &poly[i]));
            let s1: Vec<Q> = a.iter().map(|x| cross(&d, &subp(x, &p))).collect();
            let s2: Vec<Q> = b.iter().map(|x| cross(&d, &subp(x, &p))).collect();
            let (mx1, mn1) = (*s1.iter().max().unwrap(), *s1.iter().min().unwrap());
            let (mx2, mn2) = (*s2.iter().max().unwrap(), *s2.iter().min().unwrap());
            if (mx1.sign() <= 0 && mn2.sign() >= 0) || (mn1.sign() >= 0 && mx2.sign() <= 0) { return true; }
        }
    }
    false
}

struct Closure { sig: String, dim: usize, n: i128, vals: Vec<Q>, polys: Vec<(Placed, Vec<(Q, Q)>)>, scales: Vec<Vec<i128>>, ok: bool, info: String }

fn evalp(p: &(Aff, Aff), v: &[Q]) -> (Q, Q) { (p.0.eval(v), p.1.eval(v)) }

fn tiles_of(p: &Placed, sc: &[i128]) -> i128 {
    match p.kind { 0 => sc[0] * sc[0], 1 => 2 * sc[0] * sc[1], 2 => sc[0] * sc[0] - sc[1] * sc[1], _ => 0 }
}

/// scale a rational point so that every variable is an integer; returns (vals, N)
fn candidate(e: &Enum, st: &State, obj: Option<&Aff>) -> Option<(Vec<Q>, i128)> {
    let pt = lp_feasible(&st.ineq, &st.free, st.nvar as usize, obj)?;
    let mut vals = pt;
    for (v, r) in st.elim.iter().rev() { let x = r.eval(&vals); vals[*v as usize] = x; }
    if vals.iter().any(|q| q.is_big()) { BIGPT.fetch_add(1, std::sync::atomic::Ordering::Relaxed); return None; }
    let mut den = 1i128;
    for i in 0..st.nvar as usize { den = lcm_i(den, vals[i].denom()); }
    let mut vals: Vec<Q> = vals.iter().map(|x| x.mul(Q::int(den))).collect();
    let mut gg = 0i128; for i in 0..st.nvar as usize { gg = gcd_i(gg, vals[i].numer()); }
    if gg > 1 { for x in vals.iter_mut() { *x = x.div(Q::int(gg)); } }
    let mut n = 0i128;
    for p in &st.pieces { let sc: Vec<i128> = p.sc.iter().map(|a| a.eval(&vals).numer()).collect(); n += tiles_of(p, &sc); }
    let _ = e;
    Some((vals, n))
}


/// is W in the numerical semigroup <a,b> (W >= 0)?  returns (alpha,beta) with alpha*a+beta*b = W
fn in_sg(w: i128, a: i128, b: i128) -> Option<(i128, i128)> {
    if w < 0 { return None; }
    let mut al = 0; while al * a <= w { if (w - al * a) % b == 0 { return Some((al, (w - al * a) / b)); } al += 1; }
    None
}
/// Zhang's side conditions for an eqtrap(x, l): l = k*ab (k >= 1), x - (a^2+b^2) in <a,b>
fn zhang_ok(a: i128, b: i128, x: i128, l: i128) -> bool {
    l > 0 && l % (a * b) == 0 && in_sg(x - a * a - b * b, a, b).is_some()
}
/// smallest integer point of the cone satisfying Zhang's conditions on every eqtrap piece (brute force over the free variables)
fn zhang_point(e: &Enum, st: &State, gform: &Aff) -> Option<(Vec<Q>, i128)> {
    let (a, b) = (e.fam.sides[0], e.fam.sides[1]);
    // pass 1: free variables are multiples of ab (in the pinwheel they are the leg lengths l_i = r_i*ab); pass 2: dense small range
    let d = st.free.len();
    let m1: i128 = match d { 0 | 1 => 400, 2 => 120, 3 => 40, _ => 14 };
    if let Some(r) = zhang_point_in(e, st, gform, a * b, m1) { return Some(r); }
    let m: i128 = std::env::var("ZMAX").ok().and_then(|x| x.parse().ok()).unwrap_or(match d { 0 | 1 => 4000, 2 => 600, 3 => 150, _ => 40 });
    zhang_point_in(e, st, gform, 1, m)
}
fn zhang_point_in(e: &Enum, st: &State, gform: &Aff, step: i128, m: i128) -> Option<(Vec<Q>, i128)> {
    let fam = e.fam; let (a, b) = (fam.sides[0], fam.sides[1]);
    let d = st.free.len();
    let mut cur = vec![1i128; d];
    let mut best: Option<(Vec<Q>, i128, Q)> = None;
    loop {
        let mut vals = vec![Q::ZERO; st.nvar as usize];
        for (i, &v) in st.free.iter().enumerate() { vals[v as usize] = Q::int(cur[i] * step); }
        for (v, r) in st.elim.iter().rev() { let x = r.eval(&vals); vals[*v as usize] = x; }
        let mut ok = st.ineq.iter().all(|f| f.eval(&vals).sign() > 0);
        if ok { for p in &st.pieces {
            if p.kind == 3 && p.name.starts_with("eqtrap") {
                let xs: Vec<Q> = p.sc.iter().map(|q| q.eval(&vals)).collect();
                if xs.iter().any(|q| q.denom() != 1) || !zhang_ok(a, b, xs[0].numer(), xs[1].numer()) { ok = false; break; }
            } else if p.kind == 3 { ok = false; break; }
        } }
        if ok {
            let g = gform.eval(&vals);
            if best.is_none() || g < best.as_ref().unwrap().2 { best = Some((vals, 0, g)); }
        }
        // odometer
        let mut i = 0; while i < d { cur[i] += 1; if cur[i] <= m { break; } cur[i] = 1; i += 1; }
        if i == d { break; }
    }
    best.map(|(v, n, _)| (v, n))
}

fn finish(e: &Enum, st: &State, tpoly: &[(Aff, Aff)]) -> Option<Closure> {
    let fam = e.fam;
    let mut gform = Aff::var(0); for (v, r) in &st.elim { gform = gform.subst(*v, r); }
    let mut objs: Vec<Option<Aff>> = vec![Some(gform.clone())];
    for &v in &st.free { objs.push(Some(Aff::var(v))); }
    // random small objectives: sample vertices of the cone to find a small integer point (N is not minimised by min g alone)
    let mut rng: u64 = 0x9E3779B97F4A7C15 ^ (st.free.len() as u64);
    if st.free.len() >= 2 { for _ in 0..48 {
        let mut o = Aff::zero();
        for &v in &st.free { rng = rng.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407); let w = ((rng >> 33) % 7) as i128 - 2; if w != 0 { o = o.add(&Aff::var(v).scale(Q::int(w))); } }
        o = o.add(&gform);
        objs.push(Some(o));
    } }
    let mut sum = Aff::zero(); for &v in &st.free { sum = sum.add(&Aff::var(v)); } objs.push(Some(sum));
    let mut best: Option<(Vec<Q>, i128)> = None;
    if st.pieces.iter().any(|p| p.kind == 3 && p.name.starts_with("eqtrap")) {
        best = zhang_point(e, st, &gform);
    } else {
    for o in objs {
        let r = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| candidate(e, st, o.as_ref())));
        if let Ok(Some((v, n))) = r { if best.is_none() || n < best.as_ref().unwrap().1 { best = Some((v, n)); } }
    }
    }
    let (vals, n) = best?;
    // exact macro verification
    let polys: Vec<(Placed, Vec<(Q, Q)>)> = st.pieces.iter().map(|p| {
        let pts: Vec<(Q, Q)> = p.pts.iter().map(|q| evalp(q, &vals)).collect();
        (p.clone(), pts)
    }).collect();
    if polys.iter().any(|(_, ps)| ps.iter().any(|(x, y)| x.is_big() || y.is_big())) { BIGPT.fetch_add(1, std::sync::atomic::Ordering::Relaxed); return None; }
    let hull = |p: &Placed, pts: &Vec<(Q, Q)>| -> Vec<(Q, Q)> { if p.kind == 2 { pts[..4].to_vec() } else { pts.clone() } };
    let has_eq = st.pieces.iter().any(|p| p.kind == 3);
    let mut tot = Q::ZERO; let mut bad = vec![]; let mut nondeg = true;
    let hulls: Vec<Vec<(Q, Q)>> = polys.iter().map(|(p, pts)| hull(p, pts)).collect();
    for h in &hulls { let a = area2(h); if a.is_zero() { nondeg = false; } tot = tot.add(Q::int(0).add(if a.sign() < 0 { a.neg() } else { a })); }
    for i in 0..hulls.len() { for j in i + 1..hulls.len() { if !sep(&hulls[i], &hulls[j]) { bad.push((i, j)); } } }
    let t: Vec<(Q, Q)> = tpoly.iter().map(|q| evalp(q, &vals)).collect();
    let ta = { let a = area2(&t); if a.sign() < 0 { a.neg() } else { a } };
    let mut inside = true;
    for h in &hulls { for p in h { for k in 0..3 { if cross(&subp(&t[(k + 1) % 3], &t[k]), &subp(p, &t[k])).sign() < 0 { inside = false; } } } }
    let tile_a2 = Q::int(fam.sides[2]).mul(Q::int(fam.sides[1])).mul(fam.units[0].s);
    let n = if has_eq { let r = ta.div(tile_a2); if r.denom() == 1 { r.numer() } else { 0 } } else { n };
    let area_ok = tot == ta && (has_eq || ta == tile_a2.mul(Q::int(n)));
    let ok = area_ok && bad.is_empty() && inside && nondeg;
    let scales: Vec<Vec<i128>> = st.pieces.iter().map(|p| p.sc.iter().map(|a| a.eval(&vals).numer()).collect()).collect();
    let mut names: Vec<String> = st.pieces.iter().zip(scales.iter()).map(|(p, sc)| format!("{}{:?}", p.kind, { let mut v = sc.clone(); if p.kind == 1 { v.sort(); } v })).collect(); names.sort();
    let sig = format!("{}#{}#{}", names.join(","), st.free.len(), n);
    let info = format!("area_ok={} overlaps={:?} inside={} nondeg={}", area_ok, bad, inside, nondeg);
    Some(Closure { sig, dim: st.free.len(), n, vals, polys, scales, ok, info })
}

fn write_tiles(e: &Enum, c: &Closure, path: &str, maxtiles: i128) -> Result<usize, String> {
    if c.polys.iter().any(|(p, _)| p.kind == 3 && !p.name.starts_with("eqtrap")) { return Err("eqtri pieces are not expanded (only Zhang eqtrap rows)".into()); }
    if c.n > maxtiles { return Err(format!("N={} > cap {}", c.n, maxtiles)); }
    let fam = e.fam;
    let mut out = format!("# {} tiles, each with sides ({},{},{}); template closure; each line: X0 Y0 X1 Y1 X2 Y2, a vertex is the point (X, Y*sqrt({})); written by bonfioli_template (bto)\n",
        c.n, fam.sides[0], fam.sides[1], fam.sides[2], fam.dd);
    let mut tri = |a: &(Q, Q), b: &(Q, Q), cc: &(Q, Q), out: &mut String| { out.push_str(&format!("{} {} {} {} {} {}\n", a.0, a.1, b.0, b.1, cc.0, cc.1)); };
    for (k, (p, pts)) in c.polys.iter().enumerate() {
        let sc = &c.scales[k];
        match p.kind {
            0 | 2 => {
                // triangle ladder from corner (pts[0] for tri; apex X = pts[4] with edges to the full-triangle corners for trap)
                let (o, e1, e2, s, sp) = if p.kind == 0 {
                    (pts[0], subp(&pts[1], &pts[0]), subp(&pts[2], &pts[0]), sc[0], 0)
                } else {
                    // trapezoid CCW rotated list pts[0..4], apex pts[4]; which index is Y,Z: name carries iy
                    let iy: usize = p.name.split("iy").nth(1).unwrap().parse().unwrap();
                    let yy = pts[iy]; let zz = pts[(iy + 1) % 4]; let x = pts[4];
                    (x, subp(&yy, &x), subp(&zz, &x), sc[0], sc[1])
                };
                let q = |i: i128, j: i128| -> (Q, Q) {
                    (o.0.add(e1.0.mul(Q::new(i, s))).add(e2.0.mul(Q::new(j, s))), o.1.add(e1.1.mul(Q::new(i, s))).add(e2.1.mul(Q::new(j, s))))
                };
                for i in 0..s { for j in 0..s - i {
                    if !(p.kind == 2 && i + j + 1 <= sp) { tri(&q(i, j), &q(i + 1, j), &q(i, j + 1), &mut out); }
                    if j < s - i - 1 && !(p.kind == 2 && i + j + 2 <= sp) { tri(&q(i + 1, j), &q(i, j + 1), &q(i + 1, j + 1), &mut out); }
                } }
            }
            3 => {
                // Zhang's ideal trapezoid of kk rows (ZhangTrap.trapPc): x = a^2+b^2+W0 (short side), l = kk*ab (leg).  Canonical skew frame:
                // e1 = long-base direction, e2 = e1 rotated +60 deg; row i (from the long base): basic trapezoid at (0, i*ab) (three ladder triangles
                // of scales a, b, c) + parallelogram of width W_i = W0 + (kk-1-i)*ab cut into columns of width a / b (ZhangBase.basic_real, ZhangTrap.col1/col2).
                let (a, b) = (fam.sides[0], fam.sides[1]); let cc2 = a * a + a * b + b * b;
                let (x, l) = (sc[0], sc[1]);
                if !zhang_ok(a, b, x, l) { return Err(format!("eqtrap(x={},l={}) violates Zhang's side conditions", x, l)); }
                let kk = l / (a * b); let w0 = x - a * a - b * b;
                let ell = |i: usize| -> Q { let (p0, p1) = (pts[i], pts[(i + 1) % 4]); let dx = p1.0.sub(p0.0); let dy = p1.1.sub(p0.1); dx.mul(dx).add(dy.mul(dy).mul_int(fam.dd)) };
                let il = (0..4).find(|&i| ell(i) == Q::int((x + l) * (x + l))).ok_or("long base of eqtrap not found")?;
                let (o, bb) = (pts[il], pts[(il + 1) % 4]);
                let d1 = dir_of(&Pt::new(bb.0.sub(o.0), bb.1.sub(o.1)), Q::int(x + l));
                let d2 = d1.rot(fam.units[2], fam.dd);
                let sk = |u: i128, v: i128| -> (Q, Q) { (o.0.add(d1.c.mul_int(u)).add(d2.c.mul_int(v)), o.1.add(d1.s.mul_int(u)).add(d2.s.mul_int(v))) };
                let ladder = |p0: (Q, Q), p1: (Q, Q), p2: (Q, Q), s: i128, out: &mut String| {
                    let (e1, e2) = (subp(&p1, &p0), subp(&p2, &p0));
                    let q = |i: i128, j: i128| -> (Q, Q) { (p0.0.add(e1.0.mul(Q::new(i, s))).add(e2.0.mul(Q::new(j, s))), p0.1.add(e1.1.mul(Q::new(i, s))).add(e2.1.mul(Q::new(j, s)))) };
                    let mut t = |u: &(Q, Q), v: &(Q, Q), w: &(Q, Q)| { out.push_str(&format!("{} {} {} {} {} {}\n", u.0, u.1, v.0, v.1, w.0, w.1)); };
                    for i in 0..s { for j in 0..s - i {
                        t(&q(i, j), &q(i + 1, j), &q(i, j + 1));
                        if j < s - i - 1 { t(&q(i + 1, j), &q(i, j + 1), &q(i + 1, j + 1)); }
                    } }
                };
                for i in 0..kk {
                    let h = i * a * b;
                    let (po, pe, pd, pbb, pc) = (sk(0, h), sk(a * a, h + a * b), sk(0, h + a * b), sk(cc2, h), sk(a * a + b * b, h + a * b));
                    ladder(po, pe, pd, a, &mut out);          // T1 = (O, E, D), scale a
                    ladder(pe, pbb, pc, b, &mut out);         // T2 = (E, B, C), scale b
                    ladder(pbb, po, pe, fam.sides[2], &mut out); // T3 = (B, O, E), scale c
                    let wi = w0 + (kk - 1 - i) * a * b;
                    let (al, be) = in_sg(wi, a, b).ok_or("semigroup")?;
                    let mut xx = a * a + b * b;
                    for (w, q, reps) in [(a, a, al), (b, b, be)] {
                        for _ in 0..reps {
                            let y0 = h + a * b + a * b;     // top of the row = (i+1)ab
                            let _ = y0;
                            let tl = sk(xx, h + 2 * a * b - a * b);   // top-left corner (xx, (i+1)ab)
                            let (u, wv) = (subp(&sk(xx + w, h + a * b), &tl), subp(&sk(xx + a * b, h), &tl));
                            for j in 0..q {
                                let c0 = (tl.0.add(wv.0.mul(Q::new(j, q))), tl.1.add(wv.1.mul(Q::new(j, q))));
                                let c1 = (c0.0.add(u.0), c0.1.add(u.1));
                                let c2 = (c1.0.add(wv.0.mul(Q::new(1, q))), c1.1.add(wv.1.mul(Q::new(1, q))));
                                let c3 = (c0.0.add(wv.0.mul(Q::new(1, q))), c0.1.add(wv.1.mul(Q::new(1, q))));
                                tri(&c0, &c1, &c2, &mut out); tri(&c0, &c2, &c3, &mut out);
                            }
                            xx += w;
                        }
                    }
                }
            }
            _ => {
                let (v0, v1, v3) = (pts[0], pts[1], pts[3]);
                let (pc, qc) = (sc[0], sc[1]);
                let u = subp(&v1, &v0); let w = subp(&v3, &v0);
                let pp = |i: i128, j: i128| -> (Q, Q) {
                    (v0.0.add(u.0.mul(Q::new(i, pc))).add(w.0.mul(Q::new(j, qc))), v0.1.add(u.1.mul(Q::new(i, pc))).add(w.1.mul(Q::new(j, qc))))
                };
                for i in 0..pc { for j in 0..qc {
                    let (c0, c1, c2, c3) = (pp(i, j), pp(i + 1, j), pp(i + 1, j + 1), pp(i, j + 1));
                    if p.flag { tri(&c0, &c1, &c3, &mut out); tri(&c2, &c1, &c3, &mut out); } else { tri(&c0, &c1, &c2, &mut out); tri(&c0, &c2, &c3, &mut out); }
                } }
            }
        }
    }
    let cnt = out.lines().filter(|l| !l.starts_with('#')).count();
    std::fs::write(path, out).map_err(|x| x.to_string())?;
    Ok(cnt)
}

fn parse_q(s: &str) -> Q { Q::parse(s.trim()) }

fn make_init(e: &mut Enum, fam: &Fam, tgt: &str, kind: &str, nums: &[i128]) -> State {
    let g = Aff::var(0);
    if tgt == "tile" {
        let [a, b, c] = fam.sides;
        e.initial_triangle([fam.tang[0], fam.tang[1], fam.tang[2]], [g.scale(Q::int(c)), g.scale(Q::int(a)), g.scale(Q::int(b))], [0, 0, 0], 1)
    } else if tgt == "T" {
        // gamma = 2 alpha isosceles T(g): base g v b, legs g u b, base angles alpha ; (u,v) from --fam g2a:u,v
        assert!(kind == "g2a"); let (u, v) = (nums[0], nums[1]); let b = v * v - u * u;
        let pi = fam.pi();
        e.initial_triangle([fam.tang[0], fam.tang[0], asub(pi, aadd(fam.tang[0], fam.tang[0]))],
            [g.scale(Q::int(v * b)), g.scale(Q::int(u * b)), g.scale(Q::int(u * b))], [0, 0, 0], 1)
    } else if let Some(sd) = tgt.strip_prefix("sides:") {
        // similar copy of the triangle with side lengths A,B,C (edges 0,1,2 in CCW order), scaled by g; corner angles found exactly
        let l: Vec<i128> = sd.split(',').map(|x| x.parse().unwrap()).collect();
        let mut angs = [[0i32; 3]; 3];
        for v in 0..3 { let (e0, e1, e2) = (l[v], l[(v + 1) % 3], l[(v + 2) % 3]);
            let cv = Q::new(e0 * e0 + e2 * e2 - e1 * e1, 2 * e0 * e2);
            angs[v] = fam.find_ang(cv).unwrap_or_else(|| panic!("corner angle of target vertex {} is not a lattice angle of this family", v)); }
        println!("target corner angle vectors {:?}", angs);
        e.initial_triangle(angs, [g.scale(Q::int(l[0])), g.scale(Q::int(l[1])), g.scale(Q::int(l[2]))], [0, 0, 0], 1)
    } else {
        // --target "m,n,k;m,n,k;m,n,k;L0,L1,L2"   (angles of the three corners, edge lengths as multiples of g; edge 0 along angle 0)
        let parts: Vec<&str> = tgt.split(';').collect();
        let ang = |s: &str| -> Ang { let v: Vec<i32> = s.split(',').map(|x| x.parse().unwrap()).collect(); [v[0], v[1], v[2]] };
        let ls: Vec<Q> = parts[3].split(',').map(parse_q).collect();
        e.initial_triangle([ang(parts[0]), ang(parts[1]), ang(parts[2])], [g.scale(ls[0]), g.scale(ls[1]), g.scale(ls[2])], [0, 0, 0], 1)
    }
    
}

fn main() {
    std::panic::set_hook(Box::new(|info| { let m = info.to_string(); if !m.contains("overflow") && !m.contains("simplex iteration cap") { eprintln!("{}", m); } }));
    let args: Vec<String> = std::env::args().skip(1).collect();
    let get = |k: &str| -> Option<String> { args.iter().position(|a| a == k).and_then(|i| args.get(i + 1).cloned()) };
    let has = |k: &str| args.iter().any(|a| a == k);
    if has("--lptest") {
        let (x, y, z) = (Aff::var(0), Aff::var(1), Aff::var(2));
        let q = |n| Q::int(n);
        let t1 = vec![x.sub(&y), y.sub(&x)];
        println!("x>y,y>x : {:?}", lp_feasible(&t1, &[0, 1], 3, None).is_some());
        let t2 = vec![x.sub(&y.scale(q(2))), y.sub(&z.scale(q(2))), z.sub(&x.scale(q(2)))];
        println!("x>2y,y>2z,z>2x : {:?}", lp_feasible(&t2, &[0, 1, 2], 3, None).is_some());
        let t3 = vec![x.sub(&y.scale(q(2))), y.sub(&z.scale(q(2))), z.sub(&x.scale(Q::new(1, 5)))];
        println!("x>2y,y>2z,z>x/5 (feasible): {:?}", lp_feasible(&t3, &[0, 1, 2], 3, None).map(|p| p.iter().map(|v| v.to_string()).collect::<Vec<_>>()));
        let t4 = vec![x.sub(&y.scale(q(2))), y.sub(&z.scale(q(2))), z.sub(&x.scale(Q::new(1, 9))), x.scale(q(-1)).add(&z.scale(q(1)))];
        println!("... and z>x : {:?}", lp_feasible(&t4, &[0, 1, 2], 3, None).is_some());
        return;
    }
    let famspec = get("--fam").expect("--fam kind:a,b,c | g2a:u,v");
    let (kind, rest) = famspec.split_once(':').unwrap();
    let nums: Vec<i128> = rest.split(',').map(|x| x.parse().unwrap()).collect();
    let mk_fam = || -> Fam { if kind == "g2a" { make_fam("g2a", nums[0] * nums[0], nums[1] * nums[1] - nums[0] * nums[0], nums[0] * nums[1]) } else { make_fam(kind, nums[0], nums[1], nums[2]) } };
    let fam = mk_fam();
    let k: usize = get("--K").map(|x| x.parse().unwrap()).unwrap_or(4);
    let cfg = Cfg { bricks: has("--bricks"), traps: has("--traps"), k, want_all: has("--all"), tl: get("--tl").map(|x| x.parse().unwrap()).unwrap_or(600.0),
        maxnodes: get("--maxnodes").map(|x| x.parse().unwrap()).unwrap_or(0),
        minp: get("--minp").map(|x| x.parse().unwrap()).unwrap_or(0), mindim: get("--mindim").map(|x| x.parse().unwrap()).unwrap_or(0), maxbricks: get("--maxbricks").map(|x| x.parse().unwrap()).unwrap_or(99), eqshape: has("--eqshape"), noeqtri: has("--noeqtri"), nobound: has("--nobound"), sample_depth: get("--sample").map(|x| x.parse().unwrap()).unwrap_or(0), sample_cap: get("--cap").map(|x| x.parse().unwrap()).unwrap_or(0), split: has("--split") };
    let mut e = Enum::new(&fam, cfg);
    let pi = fam.pi(); let _ = pi;
    let tgt = get("--target").unwrap_or("T".into());
    let init = make_init(&mut e, &fam, &tgt, kind, &nums);
    let tpoly = e.tpoly.clone();
    println!("family {} D={} q={} tile angles {:?}; target {}; K={} bricks={} traps={} fill-set {} entries", fam.name, fam.dd, fam.q, fam.tang, tgt, k, e.cfg.bricks, e.cfg.traps, e.fill.len());
    // replay mode
    if let Some(h) = get("--replay") {
        let steps: Vec<(u16, u8, u16)> = h.split(',').map(|x| { let v: Vec<&str> = x.split(':').collect(); (v[0].parse().unwrap(), v[1].parse().unwrap(), v[2].parse().unwrap()) }).collect();
        let mut st = init;
        for (n, (si, case, kid)) in steps.iter().enumerate() {
            let kids = e.expand(&st, n);
            match kids.iter().filter(|k| k.0 == *si && k.1 == *case).nth(*kid as usize) {
                Some((s2, c2, s)) if s2 == si && c2 == case => { st = s.clone(); if has("--dbg") { println!("step {} poly angles(deg): {:?}", n + 1, st.poly.iter().map(|v| (fam.val(v.ang) * 180.0 / std::f64::consts::PI * 100.0).round() / 100.0).collect::<Vec<_>>()); } }
                _ => { println!("REPLAY FAILS at step {} (piece {}): template does not extend at this family ({} kids)", n + 1, n + 1, kids.len()); return; }
            }
        }
        if st.poly.len() < 3 {
            println!("REPLAY CLOSES: dim {} ineq {}", st.free.len(), st.ineq.len());
            if let Some(c) = finish(&e, &st, &tpoly) { println!("  integer point N={} ok={} {}", c.n, c.ok, c.info); }
            if has("--cone") {
                let mut gform = Aff::var(0); for (v, r) in &st.elim { gform = gform.subst(*v, r); }
                println!("CONE free={:?}", st.free);
                println!("CONE g = {}", gform.show());
                for (i, p) in st.pieces.iter().enumerate() { println!("CONE piece {} {} kind={} sc = {}", i, p.name.split('|').next().unwrap(), p.kind, p.sc.iter().map(|a| a.show()).collect::<Vec<_>>().join(" ; ")); }
                for f in &st.ineq { println!("CONE ineq {} > 0", f.show()); }
            }
        } else { println!("REPLAY ends with an open frontier of {} vertices", st.poly.len()); }
        return;
    }
    let iter = has("--iter");
    let ks: Vec<usize> = if iter { (1..=k).collect() } else { vec![k] };
    let outdir = get("--out").unwrap_or(".".into());
    let bte = get("--bte");
    let maxtiles: i128 = get("--maxtiles").map(|x| x.parse().unwrap()).unwrap_or(400000);
    let mut seen: HashSet<String> = HashSet::new();
    let mut nclosed = 0usize;
    let oneper = has("--oneper"); let mut expanded: HashSet<i128> = HashSet::new();
    let nthreads: usize = get("--threads").map(|x| x.parse().unwrap()).unwrap_or(1).max(1);
    for kk in ks {
        e.cfg.k = kk;
        let t1 = std::time::Instant::now();
        let shared = Shared { claimed: std::sync::Mutex::new(HashSet::new()), stop: std::sync::atomic::AtomicBool::new(false) };
        struct Ctr { nodes: u64, lps: u64, dead: u64, bp: u64, lpinf: u64, ovf: u64, filt: u64, capped: u64, timed: bool, dn: Vec<u64>, splits: u64, promoted: u64 }
        type Fin = (Vec<String>, usize, Vec<String>, Option<Closure>);
        let results: Vec<(Ctr, Vec<Fin>)> = std::thread::scope(|sc| {
            let hs: Vec<_> = (0..nthreads).map(|_| {
                let (shared, mk_fam, cfg0, tgt_r, kind_r, nums_r) = (&shared, &mk_fam, e.cfg.clone(), &tgt, kind, &nums);
                sc.spawn(move || {
                    let fam_t = mk_fam();
                    let mut et = Enum::new(&fam_t, cfg0);
                    et.shared = Some(shared);
                    let init_t = make_init(&mut et, &fam_t, tgt_r, kind_r, nums_r);
                    et.depth_nodes = vec![0; et.cfg.k + 2];
                    et.search(init_t, 0);
                    let tp = et.tpoly.clone();
                    let closed = std::mem::take(&mut et.closed);
                    let mut fin: Vec<Fin> = Vec::new();
                    for st in &closed {
                        let hist: Vec<String> = st.hist.iter().map(|(a, b, c)| format!("{}:{}:{}", a, b, c)).collect();
                        let names: Vec<String> = st.pieces.iter().map(|p| p.name.split('|').next().unwrap().to_string()).collect();
                        let c = finish(&et, st, &tp);
                        fin.push((hist, st.pieces.len(), names, c));
                    }
                    (Ctr { nodes: et.nodes, lps: et.lps, dead: et.dead_wedge, bp: et.bound_pruned, lpinf: et.lp_inf, ovf: et.ovf, filt: et.filtered, capped: et.capped, timed: et.timed_out, dn: et.depth_nodes.clone(), splits: et.splits, promoted: PROMOTED.with(|c| c.get()) }, fin)
                })
            }).collect();
            hs.into_iter().map(|h| h.join().unwrap()).collect()
        });
        let mut tot = Ctr { nodes: 0, lps: 0, dead: 0, bp: 0, lpinf: 0, ovf: 0, filt: 0, capped: 0, timed: false, dn: vec![0; kk + 2], splits: 0, promoted: 0 };
        let mut fins: Vec<Fin> = Vec::new();
        for (c, f) in results {
            tot.nodes += c.nodes; tot.lps += c.lps; tot.dead += c.dead; tot.bp += c.bp; tot.lpinf += c.lpinf; tot.ovf += c.ovf; tot.filt += c.filt; tot.capped += c.capped;
            tot.timed |= c.timed; tot.splits += c.splits; tot.promoted += c.promoted; for (i, x) in c.dn.iter().enumerate() { if i < tot.dn.len() { tot.dn[i] += x; } }
            fins.extend(f);
        }
        e.timed_out = tot.timed;
        println!("K={} threads={} split={} capped={} filtered={} nodes={} lps={} dead_wedge={} bound_pruned={} lp_infeasible={} ovf={} promoted={} bigpt={} splits_taken={} closed={} exhausted={} time={:.1}s depth_nodes={:?}",
            kk, nthreads, e.cfg.split, tot.capped, tot.filt, tot.nodes, tot.lps, tot.dead, tot.bp, tot.lpinf, tot.ovf, tot.promoted, BIGPT.load(std::sync::atomic::Ordering::Relaxed), tot.splits, fins.len(), !tot.timed, t1.elapsed().as_secs_f64(), tot.dn);
        for (hist, npieces, names, cl) in fins {
            match cl {
                None => println!("  CLOSED(no point) hist={}", hist.join(",")),
                Some(c) => {
                    if !seen.insert(c.sig.clone()) { continue; }
                    nclosed += 1;
                    println!("  CLOSED pieces={} dim={} N={} macro_verified={} {} pieces={:?}\n    hist={}", npieces, c.dim, c.n, c.ok, if c.ok { String::new() } else { c.info.clone() }, names, hist.join(","));
                    println!("    scales={:?}", c.scales);
                    if c.ok && (!oneper || expanded.insert(c.n)) {
                        let path = format!("{}/closure_{}_{}.txt", outdir, kk, nclosed);
                        match write_tiles(&e, &c, &path, maxtiles) {
                            Ok(cnt) => {
                                println!("    tiles written: {} ({} tiles) ", path, cnt);
                                if let Some(b) = &bte {
                                    let o = std::process::Command::new(b).arg("verify").arg(&path).output().unwrap();
                                    println!("    bte verify: {}", String::from_utf8_lossy(&o.stdout).trim());
                                }
                            }
                            Err(m) => println!("    tiles not written: {}", m),
                        }
                    }
                }
            }
        }
        if e.timed_out { println!("TIME/NODE LIMIT hit at K={}", kk); break; }
    }
    println!("distinct closures: {}", nclosed);
}
