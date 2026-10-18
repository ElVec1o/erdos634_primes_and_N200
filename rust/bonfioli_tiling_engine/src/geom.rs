//! Tile specification, target triangle, instance-file parsing.  All exact.
use crate::field::*;

#[derive(Clone, Copy, Debug)]
pub struct Slot { pub l1: i128, pub l2: i128, pub l3: i128, pub kind: usize, pub psi: Dir, pub k1: usize, pub k2: usize, pub k3: usize }
// kind = index (0,1,2) of the side l3 (= index of the angle at the slot vertex, angles are named by their opposite side)
// k1,k2,k3 = side indices of l1,l2,l3

#[derive(Clone, Debug)]
pub struct Spec {
    pub sides: [i128; 3],
    pub dd: i128,       // squarefree part D of 16*Area^2
    pub sd: f64,        // sqrt(D)
    pub slots: [Slot; 6],
    pub ang: [Dir; 3],  // ang[k] = angle opposite side k, as a unit direction (cos, sin)
}
pub const SIX: [(usize, usize, usize); 6] = [(0, 2, 1), (2, 0, 1), (0, 1, 2), (1, 0, 2), (2, 1, 0), (1, 2, 0)];

impl Spec {
    pub fn new(a: i128, b: i128, c: i128) -> Spec {
        let s = [a, b, c];
        let k = (a + b + c) * (-a + b + c) * (a - b + c) * (a + b - c);
        assert!(k > 0, "degenerate tile");
        let (f, dd) = squarefree_split(k as u128);
        let ang_of = |k1: usize, k2: usize, k3: usize| -> Dir {
            let (l1, l2, l3) = (s[k1], s[k2], s[k3]);
            Dir { c: Q::new(l1 * l1 + l2 * l2 - l3 * l3, 2 * l1 * l2), s: Q::new(f as i128, 2 * l1 * l2) }
        };
        let mut slots = [Slot { l1: 0, l2: 0, l3: 0, kind: 0, psi: Dir { c: Q::ZERO, s: Q::ZERO }, k1: 0, k2: 0, k3: 0 }; 6];
        for (i, &(k1, k2, k3)) in SIX.iter().enumerate() {
            slots[i] = Slot { l1: s[k1], l2: s[k2], l3: s[k3], kind: k3, psi: ang_of(k1, k2, k3), k1, k2, k3 };
        }
        let ang = [ang_of(1, 2, 0), ang_of(2, 0, 1), ang_of(0, 1, 2)];
        for d in ang.iter() { assert!(d.c.mul(d.c).add(d.s.mul(d.s).mul_int(dd as i128)) == Q::ONE); }
        Spec { sides: s, dd: dd as i128, sd: (dd as f64).sqrt(), slots, ang }
    }
    pub fn tile_area2(&self) -> Q { // 2*Area / sqrt(D) = a*b*sin(C)/sqrt(D) = a*b*s_C
        Q::int(self.sides[0] * self.sides[1]).mul(self.ang[2].s)
    }
}

#[derive(Clone, Debug)]
pub struct Target { pub v: [Pt; 3], pub len: [Q; 3], pub dir: [Dir; 3] }
impl Target {
    pub fn from_points(v: [Pt; 3], dd: i128) -> Target {
        let mut v = v;
        if orient_sign(&v[0], &v[1], &v[2]) < 0 { v.swap(1, 2); }
        assert!(orient_sign(&v[0], &v[1], &v[2]) > 0, "degenerate target");
        let mut len = [Q::ZERO; 3]; let mut dir = [Dir { c: Q::ZERO, s: Q::ZERO }; 3];
        for i in 0..3 {
            let w = v[(i + 1) % 3].sub(v[i]);
            let l2 = dist2(&v[(i + 1) % 3], &v[i], dd);
            len[i] = q_sqrt(l2).unwrap_or_else(|| panic!("target side {} has irrational length (squared {})", i, l2));
            dir[i] = dir_of(&w, len[i]);
        }
        Target { v, len, dir }
    }
    /// mrv2 convention: T0=(0,0), T1=(ga,0), T2 at distance gc from T0 and gb from T1
    pub fn from_sides(ga: Q, gb: Q, gc: Q, dd: i128) -> Target {
        let cx = ga.mul(ga).add(gc.mul(gc)).sub(gb.mul(gb)).div(ga.mul_int(2));
        let cy2 = gc.mul(gc).sub(cx.mul(cx));
        let q2 = cy2.div(Q::int(dd));
        let cy = q_sqrt(q2).unwrap_or_else(|| panic!("target apex height^2/D = {} is not a rational square (D={})", q2, dd));
        Target::from_points([Pt::new(Q::ZERO, Q::ZERO), Pt::new(ga, Q::ZERO), Pt::new(cx, cy)], dd)
    }
    pub fn contains(&self, p: &Pt) -> bool { (0..3).all(|i| orient_sign(&self.v[i], &self.v[(i + 1) % 3], p) >= 0) }
    pub fn area2(&self) -> Q { orient(&self.v[0], &self.v[1], &self.v[2]) }
}

pub struct Instance { pub spec: Spec, pub n: usize, pub target: Target, pub name: String, pub d_declared: i128 }

/// Instance file (compatible with the head of the project's instance format so that code/guard_run.sh can read D, tile, N):
///   line 1: D        line 2: a b c        line 3: N        line 4: WALKS   (the guard stops reading here)
///   then: `TARGET ga gb gc`  or  `TARGETPTS x0 y0 x1 y1 x2 y2`  (vertices (x, y*sqrt(D)), rationals)
pub fn parse_instance(path: &str) -> Instance {
    let txt = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("cannot read {}: {}", path, e));
    let lines: Vec<&str> = txt.lines().map(|l| l.trim()).filter(|l| !l.is_empty() && !l.starts_with('#')).collect();
    let d_declared: i128 = lines[0].parse().expect("line 1 must be D");
    let t: Vec<i128> = lines[1].split_whitespace().map(|x| x.parse().expect("tile")).collect();
    let n: usize = lines[2].parse().expect("line 3 must be N");
    let spec = Spec::new(t[0], t[1], t[2]);
    assert!(spec.dd == d_declared, "instance declares D={} but the tile has D={}", d_declared, spec.dd);
    let mut target: Option<Target> = None;
    for l in &lines[3..] {
        let w: Vec<&str> = l.split_whitespace().collect();
        match w[0] {
            "TARGET" => target = Some(Target::from_sides(Q::parse(w[1]), Q::parse(w[2]), Q::parse(w[3]), spec.dd)),
            "TARGETPTS" => { let q: Vec<Q> = w[1..7].iter().map(|x| Q::parse(x)).collect(); target = Some(Target::from_points([Pt::new(q[0], q[1]), Pt::new(q[2], q[3]), Pt::new(q[4], q[5])], spec.dd)); }
            _ => {}
        }
    }
    let target = target.expect("instance has no TARGET line");
    // area check: N * tile area == target area
    let lhs = Q::int(n as i128).mul(spec.tile_area2());
    assert!(lhs == target.area2(), "N * tile area != target area ({} vs {})", lhs, target.area2());
    Instance { spec, n, target, name: path.to_string(), d_declared }
}
