//! Exact verifier: a file of triangles (X0 Y0 X1 Y1 X2 Y2), vertex = (X, Y*sqrt(D)), or the OBLIQUE format.
//! Checks, all in exact arithmetic over Q(sqrt D):
//!  (1) every tile is non-degenerate and all tiles have the same three squared side lengths (and the declared ones, if the header has them);
//!  (2) the convex hull of all vertices is a triangle T (the target; read off the tiling, not from the header);
//!  (3) tiles pairwise interior-disjoint (a separating edge line exists);
//!  (4) sum of tile areas == area of T  ==>  (1)-(4) imply the tiles are a dissection of T into congruent triangles.
use crate::field::*;
use std::cmp::Ordering;

pub struct Tiling { pub d: i128, pub tiles: Vec<[Pt; 3]>, pub header: String }

fn read_text(path: &str) -> String {
    if path.ends_with(".gz") {
        let o = std::process::Command::new("gzip").arg("-dc").arg(path).output().expect("gzip");
        String::from_utf8(o.stdout).unwrap()
    } else { std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{}: {}", path, e)) }
}

pub fn load(path: &str) -> Tiling {
    let txt = read_text(path);
    let mut header = String::new();
    let mut rows: Vec<Vec<Q>> = Vec::new();
    for l in txt.lines() {
        if l.starts_with('#') { header.push_str(l); header.push('\n'); continue; }
        let w: Vec<&str> = l.split_whitespace().collect();
        if w.len() != 6 { continue; }
        rows.push(w.iter().map(|x| Q::parse(x)).collect());
    }
    // D: "sqrt(15)" or "sqrt55" or "D = 11"
    let find_d = |h: &str| -> Option<i128> {
        let b = h.as_bytes();
        let mut best = None;
        let mut i = 0;
        while let Some(p) = h[i..].find("sqrt") {
            let mut j = i + p + 4;
            if j < b.len() && (b[j] == b'(' || b[j] == b' ') { j += 1; }
            let st = j;
            while j < b.len() && b[j].is_ascii_digit() { j += 1; }
            if j > st { best = h[st..j].parse::<i128>().ok(); break; }
            i += p + 4;
        }
        if best.is_none() { if let Some(p) = h.find("D = ") { let st = p + 4; let mut j = st; while j < b.len() && b[j].is_ascii_digit() { j += 1; } best = h[st..j].parse::<i128>().ok(); } }
        best
    };
    let d = find_d(&header).unwrap_or_else(|| panic!("{}: no sqrt(D) in the header", path));
    let oblique = header.contains("OBLIQUE");
    let (mut u, mut v) = (0i128, 0i128);
    if oblique {
        let p = header.find("(u,v)=(").expect("oblique header lacks (u,v)");
        let rest = &header[p + 7..]; let e = rest.find(')').unwrap();
        let uv: Vec<i128> = rest[..e].split(',').map(|x| x.trim().parse().unwrap()).collect();
        u = uv[0]; v = uv[1];
    }
    let conv = |x: Q, y: Q| -> Pt { if oblique { // x + y w, w = (v + i sqrt D)/(2u)  ->  (x + y v/(2u), y/(2u))
            Pt::new(x.add(y.mul(Q::new(v, 2 * u))), y.mul(Q::new(1, 2 * u))) } else { Pt::new(x, y) } };
    let tiles = rows.iter().map(|r| [conv(r[0], r[1]), conv(r[2], r[3]), conv(r[4], r[5])]).collect();
    Tiling { d, tiles, header }
}

fn sat_disjoint(a: &[Pt; 3], b: &[Pt; 3]) -> bool {
    for (p, q) in [(a, b), (b, a)] {
        for i in 0..3 {
            if (0..3).all(|j| orient_sign(&p[i], &p[(i + 1) % 3], &q[j]) <= 0) { return true; }
        }
    }
    false
}

pub struct Report { pub n: usize, pub congruent: bool, pub hull3: bool, pub disjoint: bool, pub bad_pairs: usize, pub area: bool, pub sides2: [Q; 3], pub d: i128, pub target: Vec<Pt>, pub pairs_tested: u64 }
impl Report { pub fn ok(&self) -> bool { self.congruent && self.hull3 && self.disjoint && self.area } }

pub fn verify(t: &mut Tiling) -> Report {
    let dd = t.d; let n = t.tiles.len();
    let mut area_sum = Q::ZERO; let mut congruent = true;
    let mut sides2: [Q; 3] = [Q::ZERO; 3]; let mut tile_area: Option<Q> = None;
    for (i, tl) in t.tiles.iter_mut().enumerate() {
        let o = orient(&tl[0], &tl[1], &tl[2]);
        assert!(!o.is_zero(), "degenerate tile {}", i);
        if o.sign() < 0 { tl.swap(1, 2); }
        let o = orient(&tl[0], &tl[1], &tl[2]);
        let mut s = [dist2(&tl[0], &tl[1], dd), dist2(&tl[1], &tl[2], dd), dist2(&tl[0], &tl[2], dd)];
        s.sort();
        if i == 0 { sides2 = s; tile_area = Some(o); } else if s != sides2 || Some(o) != tile_area { congruent = false; }
        area_sum = area_sum.add(o);
    }
    // convex hull (monotone chain, strict)
    let mut pts: Vec<Pt> = t.tiles.iter().flat_map(|x| x.iter().cloned()).collect();
    pts.sort_by(|a, b| a.x.cmp(&b.x).then(a.y.cmp(&b.y))); pts.dedup();
    let mut hull: Vec<Pt> = Vec::new();
    for pass in 0..2 {
        let start = hull.len();
        let it: Box<dyn Iterator<Item = &Pt>> = if pass == 0 { Box::new(pts.iter()) } else { Box::new(pts.iter().rev()) };
        for p in it {
            while hull.len() >= start + 2 && orient_sign(&hull[hull.len() - 2], &hull[hull.len() - 1], p) <= 0 { hull.pop(); }
            hull.push(*p);
        }
        hull.pop();
    }
    let hull3 = hull.len() == 3;
    let area = hull3 && orient(&hull[0], &hull[1], &hull[2]) == area_sum;
    // pairwise disjointness: sweep on xmin (f64 bbox with margin), exact SAT on candidates
    let sd = (dd as f64).sqrt();
    let bb: Vec<[f64; 4]> = t.tiles.iter().map(|tl| {
        let xs: Vec<f64> = tl.iter().map(|p| p.fx()).collect(); let ys: Vec<f64> = tl.iter().map(|p| p.fy(sd)).collect();
        [xs.iter().cloned().fold(f64::MAX, f64::min), ys.iter().cloned().fold(f64::MAX, f64::min), xs.iter().cloned().fold(f64::MIN, f64::max), ys.iter().cloned().fold(f64::MIN, f64::max)]
    }).collect();
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| bb[a][0].partial_cmp(&bb[b][0]).unwrap_or(Ordering::Equal));
    let (mut bad, mut tested) = (0usize, 0u64);
    let m = 1e-7 * (1.0 + bb.iter().map(|b| b[2].abs().max(b[3].abs())).fold(0.0, f64::max));
    for ii in 0..n {
        let i = order[ii];
        for jj in ii + 1..n {
            let j = order[jj];
            if bb[j][0] > bb[i][2] + m { break; }
            if bb[j][1] > bb[i][3] + m || bb[i][1] > bb[j][3] + m { continue; }
            tested += 1;
            if !sat_disjoint(&t.tiles[i], &t.tiles[j]) { bad += 1; }
        }
    }
    Report { n, congruent, hull3, disjoint: bad == 0, bad_pairs: bad, area, sides2, d: dd, target: hull, pairs_tested: tested }
}
