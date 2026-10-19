//! Sparse affine forms over Q in integer-indexed variables, and the exact two-phase simplex.
use crate::field::Q;
pub type Var = u16;

#[derive(Clone, Debug, PartialEq)]
pub struct Aff { pub c: Q, pub t: Vec<(Var, Q)> }

impl Aff {
    pub fn zero() -> Aff { Aff { c: Q::ZERO, t: Vec::new() } }
    pub fn cst(c: Q) -> Aff { Aff { c, t: Vec::new() } }
    pub fn var(v: Var) -> Aff { Aff { c: Q::ZERO, t: vec![(v, Q::ONE)] } }
    pub fn is_const(&self) -> bool { self.t.is_empty() }
    pub fn coef(&self, v: Var) -> Q { match self.t.binary_search_by_key(&v, |x| x.0) { Ok(i) => self.t[i].1, Err(_) => Q::ZERO } }
    pub fn add(&self, o: &Aff) -> Aff { self.lin(Q::ONE, o) }
    pub fn sub(&self, o: &Aff) -> Aff { self.lin(Q::ONE.neg(), o) }
    /// self + k*o
    pub fn lin(&self, k: Q, o: &Aff) -> Aff {
        let mut t = Vec::with_capacity(self.t.len() + o.t.len());
        let (mut i, mut j) = (0, 0);
        while i < self.t.len() || j < o.t.len() {
            if j >= o.t.len() || (i < self.t.len() && self.t[i].0 < o.t[j].0) { t.push(self.t[i]); i += 1; }
            else if i >= self.t.len() || o.t[j].0 < self.t[i].0 { let v = o.t[j].1.mul(k); if !v.is_zero() { t.push((o.t[j].0, v)); } j += 1; }
            else { let v = self.t[i].1.add(o.t[j].1.mul(k)); if !v.is_zero() { t.push((self.t[i].0, v)); } i += 1; j += 1; }
        }
        Aff { c: self.c.add(o.c.mul(k)), t }
    }
    pub fn scale(&self, k: Q) -> Aff {
        if k.is_zero() { return Aff::zero(); }
        Aff { c: self.c.mul(k), t: self.t.iter().map(|&(v, q)| (v, q.mul(k))).collect() }
    }
    pub fn addc(&self, k: Q) -> Aff { Aff { c: self.c.add(k), t: self.t.clone() } }
    pub fn subst(&self, v: Var, f: &Aff) -> Aff {
        match self.t.binary_search_by_key(&v, |x| x.0) {
            Err(_) => self.clone(),
            Ok(i) => { let k = self.t[i].1; let mut r = self.clone(); r.t.remove(i); r.lin(k, f) }
        }
    }
    pub fn eval(&self, pt: &[Q]) -> Q { let mut s = self.c; for &(v, q) in &self.t { s = s.add(q.mul(pt[v as usize])); } s }
    pub fn max_var(&self) -> Option<Var> { self.t.last().map(|x| x.0) }
    pub fn show(&self) -> String {
        let mut s = format!("{}", self.c);
        for &(v, q) in &self.t { s.push_str(&format!(" + {}*x{}", q, v)); }
        s
    }
}

/// Is there x >= 1 (componentwise on `free`) with every form > 0 ?  (the forms are homogeneous or not; we ask  form(x) >= 1
/// after the shift x = 1 + y, y >= 0).  Returns the point as a dense vector indexed by Var (entries of non-free vars = 0).
/// `minimize`: optional linear objective (an Aff) to minimise over the feasible set (point returned is optimal if bounded).
pub fn lp_feasible(forms: &[Aff], free: &[Var], nvars: usize, minimize: Option<&Aff>) -> Option<Vec<Q>> {
    let n = free.len();
    let mut idx = vec![usize::MAX; nvars.max(1)];
    for (i, &v) in free.iter().enumerate() { idx[v as usize] = i; }
    // rows
    struct Row { a: Vec<Q>, b: Q }
    let mut rows: Vec<Row> = Vec::new();
    for f in forms {
        if f.t.is_empty() { if f.c.sign() > 0 { continue; } else { return None; } }
        // all coefficients >= 0 and constant >= 0 : implied by x >= 1 (since sum coef*x >= sum coef >= ... need >=1)? only if
        // c + sum a_i >= 1 at x=1 and a_i>=0: then holds for all x>=1.  drop.
        let mut a = vec![Q::ZERO; n]; let mut s1 = f.c; let mut allpos = true;
        for &(v, q) in &f.t { a[idx[v as usize]] = q; s1 = s1.add(q); if q.sign() < 0 { allpos = false; } }
        if allpos && s1 >= Q::ONE { continue; }
        rows.push(Row { a, b: Q::ONE.sub(s1) });   // sum a y >= 1 - c - sum a
    }
    let m = rows.len();
    if m == 0 { let mut pt = vec![Q::ZERO; nvars]; for &v in free { pt[v as usize] = Q::ONE; } return Some(pt); }
    let nart = rows.iter().filter(|r| r.b.sign() > 0).count();
    let ncol = n + m + nart;
    let mut tab: Vec<Vec<Q>> = Vec::with_capacity(m);
    let mut basis: Vec<usize> = Vec::with_capacity(m);
    let mut ai = 0;
    for (i, r) in rows.iter().enumerate() {
        let mut row = vec![Q::ZERO; ncol + 1];
        if r.b.sign() <= 0 {      // satisfied at y = 0 : -a y + s = -b
            for j in 0..n { row[j] = r.a[j].neg(); }
            row[n + i] = Q::ONE; row[ncol] = r.b.neg(); basis.push(n + i);
        } else {                   // a y - s + t = b
            for j in 0..n { row[j] = r.a[j]; }
            row[n + i] = Q::ONE.neg(); row[n + m + ai] = Q::ONE; row[ncol] = r.b; basis.push(n + m + ai); ai += 1;
        }
        tab.push(row);
    }
    // objective row for phase 1:  reduced costs r_j = c_j - sum_{art rows} T[i][j]
    let mut obj = vec![Q::ZERO; ncol + 1];
    for i in 0..m { if basis[i] >= n + m { for j in 0..=ncol { obj[j] = obj[j].sub(tab[i][j]); } } }
    for j in n + m..ncol { obj[j] = Q::ZERO; }
    // obj[ncol] = -sum of artificials (neg of objective value)
    let pivot = |tab: &mut Vec<Vec<Q>>, obj: &mut Vec<Q>, basis: &mut Vec<usize>, pr: usize, pc: usize| {
        let pv = tab[pr][pc].inv();
        for j in 0..=ncol { if !tab[pr][j].is_zero() { tab[pr][j] = tab[pr][j].mul(pv); } }
        let prow = tab[pr].clone();
        for i in 0..m { if i != pr { let f = tab[i][pc]; if !f.is_zero() { for j in 0..=ncol { if !prow[j].is_zero() { tab[i][j] = tab[i][j].sub(f.mul(prow[j])); } } } } }
        let f = obj[pc]; if !f.is_zero() { for j in 0..=ncol { if !prow[j].is_zero() { obj[j] = obj[j].sub(f.mul(prow[j])); } } }
        basis[pr] = pc;
    };
    let run = |tab: &mut Vec<Vec<Q>>, obj: &mut Vec<Q>, basis: &mut Vec<usize>, allowed: usize| -> bool {
        let mut it = 0usize;
        loop {
            it += 1;
            let mut pc = usize::MAX;
            if it < 60 {
                let mut best = Q::ZERO;
                for j in 0..allowed { if obj[j].sign() < 0 && (pc == usize::MAX || obj[j] < best) { pc = j; best = obj[j]; } }
            } else { for j in 0..allowed { if obj[j].sign() < 0 { pc = j; break; } } }
            if pc == usize::MAX { return true; }
            let mut pr = usize::MAX; let mut br = Q::ZERO;
            for i in 0..m {
                if tab[i][pc].sign() > 0 {
                    let ratio = tab[i][ncol].div(tab[i][pc]);
                    if pr == usize::MAX || ratio < br || (ratio == br && basis[i] < basis[pr]) { pr = i; br = ratio; }
                }
            }
            if pr == usize::MAX { return false; }
            pivot(tab, obj, basis, pr, pc);
            if it > 5000 { panic!("simplex iteration cap"); }
        }
    };
    if nart > 0 {
        run(&mut tab, &mut obj, &mut basis, n + m + nart);
        // objective value = -obj[ncol]
        if obj[ncol].sign() != 0 { return None; }
        for i in 0..m {
            if basis[i] >= n + m {
                if let Some(pc) = (0..n + m).find(|&j| !tab[i][j].is_zero()) { pivot(&mut tab, &mut obj, &mut basis, i, pc); }
            }
        }
    }
    if let Some(mf) = minimize {
        // phase 2 over columns < n+m
        let mut cost = vec![Q::ZERO; ncol + 1];
        for &(v, q) in &mf.t { if idx[v as usize] != usize::MAX { cost[idx[v as usize]] = q; } }
        let mut o2 = cost.clone();
        for i in 0..m { let cb = cost[basis[i]]; if !cb.is_zero() { for j in 0..=ncol { o2[j] = o2[j].sub(cb.mul(tab[i][j])); } } }
        run(&mut tab, &mut o2, &mut basis, n + m);
    }
    let mut pt = vec![Q::ZERO; nvars];
    for &v in free { pt[v as usize] = Q::ONE; }
    for i in 0..m { if basis[i] < n { let v = free[basis[i]]; pt[v as usize] = Q::ONE.add(tab[i][ncol]); } }
    Some(pt)
}
