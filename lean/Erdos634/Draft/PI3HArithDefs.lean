/-
Draft/PI3HArithDefs.lean -- the EXACT decidable arithmetic layer of the pi/3 strip / level / T2 window.  Definitions only (+ small sanity lemmas).

* No floats, no `Real`, no classical `decide`: every predicate is a `Bool` function on `Nat`/`Int`, evaluated by `decide +kernel`
  in the sibling modules (`PI3HArithWindow`, `PI3HArithKill`).  Interval arithmetic = outward-rounded `Int` fixed point, scale `2^64`
  (kernel `Int`/`Nat` operations are GMP-accelerated).  `Nat.sqrt` is the only root primitive (Mathlib).
* Normalisation: target side `S = 2N`, `a + b = s`, `c = c0`, `ab = 4N`, `a - b = sqrt D`, `M = (s + sqrt D)/2`
  (longest edge), `m = 2 sqrt3 N / M` (smallest altitude), `tau = sqrt3 N`.
Soundness of the interval layer w.r.t. real numbers is NOT proved here (the predicates are Bool functions).
No sorry, no native_decide.
-/
import Mathlib.Data.Nat.Sqrt

namespace Erdos634.Draft.PI3H

/-! ### Number-theoretic predicates on the pair class -/

/-- `n` is squarefree (Bool): no `p^2 | n` for `2 <= p <= sqrt n`. -/
def sqf (n : ℕ) : Bool :=
  (List.range (Nat.sqrt n + 1)).all fun p => decide (2 ≤ p) → n % (p * p) != 0

/-- `n` is a perfect square (Bool). -/
def isSq (n : ℕ) : Bool := Nat.sqrt n * Nat.sqrt n == n

/-- Strict-inequality-free pieces of the x-type pair `(m1, m2) = (N/x, 3x)`:  the data of section 1.2. -/
structure XData where
  m1 : ℕ
  m2 : ℕ
  s : ℕ
  c0 : ℕ
  D : ℕ
  g : ℕ
  Dl : ℕ     -- Delta   = c0 / g
  Dc : ℕ     -- Delta_c = s / g
  lk : ℕ     -- l_kappa = (m1^2 - m2^2)/g = Delta_c * c0

def xdata (N x : ℕ) : XData :=
  let m1 := N / x
  let m2 := 3 * x
  let s := m1 + m2
  let c0 := m1 - m2
  let g := Nat.gcd s c0
  { m1 := m1, m2 := m2, s := s, c0 := c0, D := s * s - 16 * N, g := g, Dl := c0 / g, Dc := s / g, lk := s * c0 / g }

/-- The x-type pair of `N` with parameter `x` is **uncovered by Theorem T** and lies in the window class:
`N` odd squarefree, `5 <= x`, `x | N`, `3 x^2 < N` (`m2 < m1`), `3 ∤ x`, `3 | N/x`, `D > 0` non-square, `l_kappa <= 2N`. -/
def xUnc (N x : ℕ) : Bool :=
  let d := xdata N x
  decide (5 ≤ x) && (N % x == 0) && decide (3 * x * x < N) && (x % 3 != 0) && (d.m1 % 3 == 0) &&
    decide (16 * N < d.s * d.s) && !(isSq d.D) && decide (d.lk ≤ 2 * N)

/-- the list of `x` (x-type, uncovered) for `N`. -/
def xList (N : ℕ) : List ℕ :=
  (List.range (Nat.sqrt (N / 3) + 2)).filter fun x => xUnc N x

/-- `N` odd squarefree with at least one uncovered x-type pair: the WINDOW. -/
def inWindow (N : ℕ) : Bool := (N % 2 == 1) && sqf N && !((xList N).isEmpty)

/-- Standing arithmetic conditions C1-C8 (section 1.2, repaired as in section 0) for the pair `(N, x)`.
C8 (A/pi irrational): the trace `s (c0^2 - D)/(4 N c0)` of `2 cos A` over `Q(sqrt D)` is not an integer. -/
def xPre (N x : ℕ) : Bool :=
  let d := xdata N x
  (N % 2 == 1) && sqf N && xUnc N x &&
  -- C1
  (d.m1 * d.m2 == 3 * N) && (x % 2 == 1) &&
  -- C3, C4 (Delta > x, Delta_c > x), g = 6, Delta_c - Delta = x  (consequences for odd squarefree N)
  (d.g == 6) && decide (x < d.Dl) && decide (x < d.Dc) && (d.Dc == d.Dl + x) &&
  -- C5: Delta + Delta_c odd
  ((d.Dl + d.Dc) % 2 == 1) &&
  -- C6: N < l_kappa
  decide (N < d.lk) &&
  -- C7 (sufficient form): l_kappa sqrt3 >= 4 M follows from 3 l_kappa^2 >= 16 s^2 because M <= s (sqrt D < s)
  decide (16 * d.s * d.s ≤ 3 * d.lk * d.lk) &&
  -- C8: trace of 2cosA over Q(sqrt D) is s (c0^2 - D)/(4 N c0) (= s/c0 since c0^2 - D = 4N); not an integer
  ((d.s * (d.c0 * d.c0 - d.D)) % (4 * N * d.c0) != 0)

/-! ### Outward-rounded interval arithmetic over `Int`, scale `2^64`. -/

/-- the fixed-point unit `2^64`. -/
def ONE : Int := 18446744073709551616

/-- floor / ceiling division by a positive integer. -/
def fdiv (a b : Int) : Int := a / b
def cdiv (a b : Int) : Int := -((-a) / b)

structure Iv where
  lo : Int
  hi : Int

namespace Iv

/-- "no information" interval, returned by `div`/`sqrt` outside their domain (sound by construction). -/
def top : Iv := ⟨-(2 ^ 400 : Int), 2 ^ 400⟩

def int (n : Int) : Iv := ⟨n * ONE, n * ONE⟩
def rat (n d : Int) : Iv := ⟨fdiv (n * ONE) d, cdiv (n * ONE) d⟩
def add (x y : Iv) : Iv := ⟨x.lo + y.lo, x.hi + y.hi⟩
def sub (x y : Iv) : Iv := ⟨x.lo - y.hi, x.hi - y.lo⟩
def mul (x y : Iv) : Iv :=
  let a := x.lo * y.lo
  let b := x.lo * y.hi
  let c := x.hi * y.lo
  let d := x.hi * y.hi
  ⟨fdiv (min (min a b) (min c d)) ONE, cdiv (max (max a b) (max c d)) ONE⟩
def mulInt (x : Iv) (k : Int) : Iv := mul (int k) x
/-- division by an interval with positive lower end. -/
def div (x y : Iv) : Iv :=
  if 0 < y.lo then
    ⟨fdiv (x.lo * ONE) (if 0 ≤ x.lo then y.hi else y.lo), cdiv (x.hi * ONE) (if 0 ≤ x.hi then y.lo else y.hi)⟩
  else top
/-- square root of an interval (negative part clipped to 0). -/
def sqrt (x : Iv) : Iv :=
  ⟨(Nat.sqrt (x.lo.toNat * ONE.toNat) : Int), (Nat.sqrt (x.hi.toNat * ONE.toNat) : Int) + 1⟩
def max0 (x : Iv) : Iv := ⟨max x.lo 0, max x.hi 0⟩
def abs (x : Iv) : Iv :=
  if 0 ≤ x.lo then x else if x.hi ≤ 0 then ⟨-x.hi, -x.lo⟩ else ⟨0, max (-x.lo) x.hi⟩
/-- the degenerate interval at the upper end. -/
def atHi (x : Iv) : Iv := ⟨x.hi, x.hi⟩
def atLo (x : Iv) : Iv := ⟨x.lo, x.lo⟩

end Iv

/-- `pi` enclosed by 21 decimals: `3.14159265358979323846 <= pi <= 3.14159265358979323847`. -/
def piIv : Iv :=
  ⟨fdiv (314159265358979323846 * ONE) 100000000000000000000, cdiv (314159265358979323847 * ONE) 100000000000000000000⟩

/-! ### The common quantities `(a, M, m, sqrt3, ...)` of a pair (S = 2N) -/

structure Q where
  sqd : Iv
  a : Iv     -- M = (s + sqrt D)/2, the longest edge
  m : Iv     -- 2 sqrt3 N / M
  s3 : Iv
  nn : Iv
  S : Iv

def mkQ (N : ℕ) (d : XData) : Q :=
  let sqd := Iv.sqrt (Iv.int d.D)
  let a := Iv.div (Iv.add (Iv.int d.s) sqd) (Iv.int 2)
  let s3 := Iv.sqrt (Iv.int 3)
  { sqd := sqd, a := a, m := Iv.div (Iv.mul (Iv.mulInt s3 2) (Iv.int N)) a, s3 := s3, nn := Iv.int N, S := Iv.int (2 * N) }

/-! ### Strip lemma: exact arithmetic predicate (section 3.5) -/

/-- (I) `L0 < l_kappa`  <=>  `r M < 4N`  <=>  `r s < 8N` and `D r^2 < (8N - r s)^2`,  `r = 2N - l_kappa >= 0`.  PURE INTEGERS. -/
def stripI (N : ℕ) (d : XData) : Bool :=
  decide (d.lk ≤ 2 * N) &&
  decide ((2 * N - d.lk) * d.s < 8 * N) &&
  decide (d.D * ((2 * N - d.lk) * (2 * N - d.lk)) < (8 * N - (2 * N - d.lk) * d.s) * (8 * N - (2 * N - d.lk) * d.s))

/-- The WRONG predicate used as a control: the same with the comparison `L0 <= l_kappa` (non-strict) on (I). -/
def stripIle (N : ℕ) (d : XData) : Bool :=
  decide (d.lk ≤ 2 * N) &&
  decide ((2 * N - d.lk) * d.s ≤ 8 * N) &&
  decide (d.D * ((2 * N - d.lk) * (2 * N - d.lk)) ≤ (8 * N - (2 * N - d.lk) * d.s) * (8 * N - (2 * N - d.lk) * d.s))

/-- (II') `4 sqrt3 M / cos(theta*) <= A0 (1 - sqrt3 tan(theta*/2))`,  `t* = sqrt3 N / M^2 < 1/sqrt3` (interval-certified). -/
def stripII (N : ℕ) (d : XData) : Bool :=
  let q := mkQ N d
  let tstar := Iv.div (Iv.mul q.s3 q.nn) (Iv.mul q.a q.a)
  let sec := Iv.sqrt (Iv.add (Iv.int 1) (Iv.mul tstar tstar))
  let lhs := Iv.mul (Iv.mul (Iv.mulInt q.a 4) q.s3) sec
  let a0 := Iv.sub (Iv.mul q.s3 q.S) (Iv.mulInt q.m 2)
  let th2 := Iv.div tstar (Iv.add (Iv.int 1) sec)
  let rhs := Iv.mul a0 (Iv.sub (Iv.int 1) (Iv.mul q.s3 th2))
  decide (tstar.hi < (Iv.div (Iv.int 1) q.s3).lo) && decide (lhs.hi < rhs.lo)

/-- `stripDead N x := (I) and (II')`: the strip lemma (SL3 + Kill) kills the x-type pair. -/
def stripDead (N x : ℕ) : Bool := stripI N (xdata N x) && stripII N (xdata N x)

/-! ### Level lemma: interval predicate (section 5.4) -/

structure Cx where
  re : Iv
  im : Iv

def Cx.mul (z w : Cx) : Cx :=
  ⟨Iv.sub (Iv.mul z.re w.re) (Iv.mul z.im w.im), Iv.add (Iv.mul z.re w.im) (Iv.mul z.im w.re)⟩

/-- the six sixth roots of unity as intervals. -/
def zeta (s3 : Iv) : List Cx :=
  let half := Iv.rat 1 2
  let sh := Iv.div s3 (Iv.int 2)
  let nh := Iv.sub (Iv.int 0) half
  let nsh := Iv.sub (Iv.int 0) sh
  [⟨Iv.int 1, Iv.int 0⟩, ⟨half, sh⟩, ⟨nh, sh⟩, ⟨Iv.int (-1), Iv.int 0⟩, ⟨nh, nsh⟩, ⟨half, nsh⟩]

/-- certified reduction of `w` into the 30-degree cone by a multiple of `pi/3`: `(cos theta, |sin theta|)`. -/
def reduceCone (s3 : Iv) (w : Cx) : Option (Iv × Iv) :=
  (zeta s3).findSome? fun ze =>
    let v := w.mul ⟨ze.re, Iv.sub (Iv.int 0) ze.im⟩
    let aim := v.im.abs
    if 0 ≤ v.re.lo ∧ (Iv.mul s3 aim.atHi).hi ≤ v.re.lo then some (v.re, aim) else none

/-- The level cap `U` (every odd `u > U` is level-dead since `D <= inradius`). -/
def ucap (N : ℕ) (d : XData) : ℕ :=
  let q := mkQ N d
  let inr := Iv.div q.S (Iv.mulInt q.s3 2)
  let cheap := Iv.div (Iv.add (Iv.mul (Iv.mulInt q.a 2) inr) (Iv.div (Iv.mul (Iv.mul piIv q.a) q.a) (Iv.int 2))) (Iv.mul q.s3 q.nn)
  (cheap.hi / ONE).toNat + 1

/-- classification of the odd level `u` with `w = e^{iuA}`:  0 = ambiguous angle reduction, 1 = geometrically dead
(`Lb(theta_u) < l_kappa`), 2 = level dead (`u > H(max(0, D(theta_u, l_kappa)))`), 3 = alive. -/
def classify (N : ℕ) (d : XData) (q : Q) (u : ℕ) (w : Cx) : ℕ :=
  match reduceCone q.s3 w with
  | none => 0
  | some (cs, sn) =>
    let t := Iv.div sn cs
    let h := Iv.max0 (Iv.sub q.m (Iv.mul (Iv.mulInt q.a 2) t))
    let num := Iv.sub (Iv.mul q.s3 q.S) (Iv.mulInt h 2)
    let den := Iv.add (Iv.mul q.s3 cs) sn
    let lhi := Iv.div num.atHi den.atLo
    let lkv := Iv.int d.lk
    if lhi.hi < lkv.lo then 1
    else
      let inner := Iv.sub q.S (Iv.mul lkv (Iv.add cs (Iv.div sn q.s3)))
      let dm := Iv.max0 (Iv.div inner (Iv.mulInt q.s3 2))
      let hb := Iv.div (Iv.add (Iv.mul (Iv.mulInt q.a 2) dm) (Iv.div (Iv.mul (Iv.mul piIv q.a) q.a) (Iv.int 2))) (Iv.mul q.s3 q.nn)
      if (u : Int) * ONE > hb.hi then 2 else 3

/-- codes of the odd levels `u = u0, u0+2, ...` (`fuel` steps). -/
def levelCodes (N : ℕ) (d : XData) (q : Q) (z2 : Cx) : ℕ → ℕ → Cx → List ℕ
  | 0, _, _ => []
  | fuel + 1, u, w => classify N d q u w :: levelCodes N d q z2 fuel (u + 2) (w.mul z2)

/-- `e^{iA}` as an interval complex number. -/
def zA (d : XData) (q : Q) : Cx :=
  let sq := Iv.sqrt (Iv.int d.D)
  let a := Iv.div (Iv.add (Iv.int d.s) sq) (Iv.int 2)
  let b := Iv.div (Iv.sub (Iv.int d.s) sq) (Iv.int 2)
  let c := Iv.int d.c0
  let cosa := Iv.div (Iv.sub (Iv.add (Iv.mul b b) (Iv.mul c c)) (Iv.mul a a)) (Iv.mul (Iv.mul (Iv.int 2) b) c)
  let sina := Iv.div (Iv.mul a q.s3) (Iv.mul (Iv.int 2) c)
  ⟨cosa, sina⟩

/-- the classification codes of all odd levels `1, 3, ..., <= U` for the pair `(N, x)`. -/
def codes (N x : ℕ) : List ℕ :=
  let d := xdata N x
  let q := mkQ N d
  let z := zA d q
  levelCodes N d q (z.mul z) ((ucap N d + 1) / 2) 1 z

/-- `levelKill N x`: every odd level is geometrically dead or level dead (no ambiguous reduction, none alive). -/
def levelKill (N x : ℕ) : Bool := (codes N x).all fun c => c == 1 || c == 2

/-- number of entries of a code list equal to `c`. -/
def cnt (c : ℕ) (l : List ℕ) : ℕ := (l.filter fun e => e == c).length

/-- `pairKill N x`: the x-type pair is killed by strip or by level + T2. -/
def pairKill (N x : ℕ) : Bool := stripDead N x || levelKill N x

/-! ### The pair table of `N`: every pair `(m1, m2)`, `m1 m2 = 3N`, `m2 < m1 <= N` and its status -/

/-- the invariant pairs `(m1, m2)` of `N`: `m2 <= sqrt(3N)`, `3 <= m2`, `m2 | 3N`, `m2 < m1 <= N`. -/
def pairs (N : ℕ) : List (ℕ × ℕ) :=
  ((List.range (Nat.sqrt (3 * N) + 1)).filter fun m2 =>
      decide (3 ≤ m2) && (3 * N % m2 == 0) && decide (m2 < 3 * N / m2) && decide (3 * N / m2 ≤ N)).map
    fun m2 => (3 * N / m2, m2)

/-- Theorem T / existing pair table coverage `pairT` (copy of `PI3F.pairT`, defeq-checked in `PI3HArithKill`). -/
def pairT' (N m₁ m₂ : ℕ) : Bool :=
  (m₁ == N && m₂ == 3) ||
  ((decide ((m₁ + m₂) ^ 2 < 16 * N) || Nat.sqrt ((m₁ + m₂) ^ 2 - 16 * N) ^ 2 != (m₁ + m₂) ^ 2 - 16 * N) &&
    decide (2 * N * Nat.gcd (m₁ + m₂) (m₁ - m₂) < (m₁ + m₂) * (m₁ - m₂)))

/-- `D < 0` pairs are dispatched by the existing branch of `CompositeE5Gen.gapE60_of_pairs_exc`
(`¬ IsSquare D ∧ (0 ≤ D → ...)`), pinned pair `(N, 3)` by `sixty_pinned_false`. -/
def pairExisting (N m₁ m₂ : ℕ) : Bool :=
  (m₁ == N && m₂ == 3) || decide ((m₁ + m₂) ^ 2 < 16 * N)

/-- A pair is covered by (existing Lean pair kills) or Theorem T or (strip/level kill when it is an x-type pair of the window). -/
def pairCovered (N m₁ m₂ : ℕ) : Bool :=
  pairExisting N m₁ m₂ || pairT' N m₁ m₂ ||
  ((m₂ % 3 == 0) && xUnc N (m₂ / 3) && (N / (m₂ / 3) == m₁) && pairKill N (m₂ / 3))

/-- the pairs of `N` that nothing covers. -/
def uncoveredPairs (N : ℕ) : List (ℕ × ℕ) := (pairs N).filter fun p => !(pairCovered N p.1 p.2)

/-- `N` is excluded (on the arithmetic side) when it is odd squarefree and no pair is left uncovered. -/
def excluded (N : ℕ) : Bool := (N % 2 == 1) && sqf N && (uncoveredPairs N).isEmpty

end Erdos634.Draft.PI3H
