/-
Draft/SignedDecompE1.lean  In `AllThreshold`.

Paper: Proposition `prop:reframe`, part (a).  For the member `(1, f)` of the base-beta family let `(a, b, c) = (f, f^2 - 1, f^2)`
and `T_M = ABC` the isosceles triangle with apex `A`, legs `M f^3`, base `BC = M (3 f^2 - 1)`.  `Q', Q` on the base with
`|BQ'| = |CQ| = M f^2`; `Z` on the ray `AQ` beyond `Q` with `|QZ| = M f`.  Then `ABQ'`, `ACQ`, `AQ'Z` are copies of the tile
at scale `f M`, `Q'QZ` is a copy of the tile at scale `M` on the other side of the base, and
`T_M ∪ Q'QZ = ABQ' ∪ AQ'Z ∪ ACQ` with disjoint interiors on each side.

Frame: `Phi F (s, t) = s g1 + t g2` (`WFrameF`), `|g1| = |g2| = 1`, `g1 . g2 = 1 / (2 F)`; `F = f` here.  With
`u = F (F^2 - 1) t`, `v = (2 F^2 - 1) t`, `k = F^2 t`, `e = F t` the points are (frame coordinates)

    A = (0, v)   B = (u, 0)   C = (u, v + k)   Q' = (u, k)   Q = (u, v)   Z = (u + e, v)

(`v + k = (3 F^2 - 1) t`; `ptQ1` is `Q'`).  The five triangles are the convex hulls of three of these points, pushed by `Phi F`.

What is proved (all for real `F > 1`, `t > 0`):
  (i)   `union_eq`            : the union identity, as sets of the plane (images of convex hulls under `Phi F`);
  (ii)  `disjoint_*`          : the four disjointness statements of the interiors (`T` and `Q'QZ`; the three pairs of
                                `ABQ'`, `AQ'Z`, `ACQ`), through `WFrameF.disjoint_image` from separating lines;
  (iii) `d_*`                 : the eleven segment lengths as `dist (Phi F p) (Phi F q)`; `sides_*` : `HasSides` of the five
                                `triC` triangles (`triABC`, ...);
  (iv)  `signed_decomposition`: the corollary for `f, M : ℕ`, `2 ≤ f`, `1 ≤ M`, with the bridge of the carrier of `triABC`
                                to the carrier of `WtoDeltaF.DeltaTri` (the frame triangle of `T_M`).
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.WtoDeltaF
import Erdos634.Draft.S2LCore
import Erdos634.Draft.HasSidesPerm

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (interior_disj_fst interior_disj_snd)
open Erdos634.Draft.S2L (mem_hull3' tri_le tri_ge)

namespace Erdos634.Draft.SignedDecompE1
open Erdos634.Draft.WFrameF Erdos634.Draft.WBrickF Erdos634.Draft.WtoDeltaF
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)

/-! ## Coordinate forms of the hull helpers -/

theorem tri_le' {x1 y1 x2 y2 x3 y3 : ℝ} (a b c : ℝ) (hA : a * x1 + b * y1 ≤ c)
    (hB : a * x2 + b * y2 ≤ c) (hC : a * x3 + b * y3 ≤ c) :
    ∀ p ∈ convexHull ℝ ({(x1, y1), (x2, y2), (x3, y3)} : Set (ℝ × ℝ)), a * p.1 + b * p.2 ≤ c :=
  tri_le (A := (x1, y1)) (B := (x2, y2)) (C := (x3, y3)) a b c hA hB hC

theorem tri_ge' {x1 y1 x2 y2 x3 y3 : ℝ} (a b c : ℝ) (hA : c ≤ a * x1 + b * y1)
    (hB : c ≤ a * x2 + b * y2) (hC : c ≤ a * x3 + b * y3) :
    ∀ p ∈ convexHull ℝ ({(x1, y1), (x2, y2), (x3, y3)} : Set (ℝ × ℝ)), c ≤ a * p.1 + b * p.2 :=
  tri_ge (A := (x1, y1)) (B := (x2, y2)) (C := (x3, y3)) a b c hA hB hC

theorem mem3 {x1 y1 x2 y2 x3 y3 : ℝ} (D a b c : ℝ) (hD : 0 < D) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hs : a + b + c = D) (p : ℝ × ℝ) (h1 : D * p.1 = a * x1 + b * x2 + c * x3)
    (h2 : D * p.2 = a * y1 + b * y2 + c * y3) :
    p ∈ convexHull ℝ ({(x1, y1), (x2, y2), (x3, y3)} : Set (ℝ × ℝ)) :=
  mem_hull3' (A := (x1, y1)) (B := (x2, y2)) (C := (x3, y3)) D a b c hD ha hb hc hs p h1 h2

/-! ## The five regions in frame coordinates (generic `u v k e`)

`u = A0 t`, `v = B0 t`, `k = F^2 t` (so `C = (u, v + k)`, `Q' = (u, k)`), `e = F t` (so `Z = (u + e, v)`);
hypotheses `0 < u`, `0 < k`, `k < v`, `0 < e`. -/

/-- `ABC`: `x ≤ u`, above `AB`, below `AC`. -/
def regABC (u v k : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ u ∧ u * v ≤ v * p.1 + u * p.2 ∧ u * (p.2 - v) ≤ k * p.1}

/-- `ABQ'`: `x ≤ u`, above `AB`, below `AQ'`. -/
def regABQ1 (u v k : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ u ∧ u * v ≤ v * p.1 + u * p.2 ∧ (v - k) * p.1 + u * p.2 ≤ u * v}

/-- `AQ'Z`: `y ≤ v`, above `AQ'`, left of `Q'Z`. -/
def regAQ1Z (u v k e : ℝ) : Set (ℝ × ℝ) :=
  {p | p.2 ≤ v ∧ u * v ≤ (v - k) * p.1 + u * p.2 ∧ (v - k) * (p.1 - u) ≤ e * (p.2 - k)}

/-- `Q'QZ`: `x ≥ u`, `y ≤ v`, right of `Q'Z`. -/
def regQ1QZ (u v k e : ℝ) : Set (ℝ × ℝ) :=
  {p | u ≤ p.1 ∧ p.2 ≤ v ∧ (v - k) * (p.1 - u) ≤ e * (p.2 - k)}

/-- `ACQ`: `x ≤ u`, `y ≥ v`, below `AC`. -/
def regACQ (u v k : ℝ) : Set (ℝ × ℝ) :=
  {p | p.1 ≤ u ∧ v ≤ p.2 ∧ u * (p.2 - v) ≤ k * p.1}

theorem hull_regABC {u v k : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) :
    convexHull ℝ ({((0 : ℝ), v), (u, (0 : ℝ)), (u, v + k)} : Set (ℝ × ℝ)) = regABC u v k := by
  have hv0 : 0 < v := by linarith
  have huk := mul_pos hu hk
  have huv := mul_pos hu hv0
  apply Set.Subset.antisymm
  · intro p hp
    have h1 := tri_le' 1 0 u (by linarith) (by linarith) (by linarith) p hp
    have h2 := tri_ge' v u (u * v) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    have h3 := tri_le' (-k) u (u * v) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    exact ⟨by linarith, by linarith, by nlinarith⟩
  · rintro p ⟨h1, h2, h3⟩
    exact mem3 (u * (k + v)) ((u - p.1) * (k + v)) (k * p.1 - u * (p.2 - v))
      (v * p.1 + u * p.2 - u * v)
      (mul_pos hu (by linarith)) (mul_nonneg (by linarith) (by linarith)) (by nlinarith) (by nlinarith)
      (by ring) p (by ring) (by ring)

theorem hull_regABQ1 {u v k : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) :
    convexHull ℝ ({((0 : ℝ), v), (u, (0 : ℝ)), (u, k)} : Set (ℝ × ℝ)) = regABQ1 u v k := by
  have hv0 : 0 < v := by linarith
  have huk := mul_pos hu hk
  have huv := mul_pos hu hv0
  apply Set.Subset.antisymm
  · intro p hp
    have h1 := tri_le' 1 0 u (by linarith) (by linarith) (by linarith) p hp
    have h2 := tri_ge' v u (u * v) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    have h3 := tri_le' (v - k) u (u * v) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro p ⟨h1, h2, h3⟩
    exact mem3 (u * k) ((u - p.1) * k) (u * v - (v - k) * p.1 - u * p.2) (v * p.1 + u * p.2 - u * v)
      (mul_pos hu hk) (mul_nonneg (by linarith) hk.le) (by nlinarith) (by nlinarith)
      (by ring) p (by ring) (by ring)

theorem hull_regAQ1Z {u v k e : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) (he : 0 < e) :
    convexHull ℝ ({((0 : ℝ), v), (u, k), (u + e, v)} : Set (ℝ × ℝ)) = regAQ1Z u v k e := by
  have hvk : 0 < v - k := by linarith
  have hev := mul_pos he hvk
  have huvk := mul_pos hu hvk
  apply Set.Subset.antisymm
  · intro p hp
    have h1 := tri_le' 0 1 v (by linarith) (by linarith) (by linarith) p hp
    have h2 := tri_ge' (v - k) u (u * v) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    have h3 := tri_le' (v - k) (-e) ((v - k) * u - e * k) (by nlinarith) (by nlinarith)
      (by nlinarith) p hp
    exact ⟨by linarith, by linarith, by nlinarith⟩
  · rintro p ⟨h1, h2, h3⟩
    exact mem3 ((v - k) * (u + e)) (e * (p.2 - k) - (v - k) * (p.1 - u)) ((v - p.2) * (u + e))
      ((v - k) * p.1 + u * p.2 - u * v)
      (mul_pos hvk (by linarith)) (by nlinarith) (mul_nonneg (by linarith) (by linarith))
      (by nlinarith) (by ring) p (by ring) (by ring)

theorem hull_regQ1QZ {u v k e : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) (he : 0 < e) :
    convexHull ℝ ({(u, k), (u, v), (u + e, v)} : Set (ℝ × ℝ)) = regQ1QZ u v k e := by
  have hvk : 0 < v - k := by linarith
  have hev := mul_pos he hvk
  apply Set.Subset.antisymm
  · intro p hp
    have h1 := tri_ge' 1 0 u (by linarith) (by linarith) (by linarith) p hp
    have h2 := tri_le' 0 1 v (by linarith) (by linarith) (by linarith) p hp
    have h3 := tri_le' (v - k) (-e) ((v - k) * u - e * k) (by nlinarith) (by nlinarith)
      (by nlinarith) p hp
    exact ⟨by linarith, by linarith, by nlinarith⟩
  · rintro p ⟨h1, h2, h3⟩
    exact mem3 (e * (v - k)) ((v - p.2) * e) (e * (p.2 - k) - (v - k) * (p.1 - u))
      ((p.1 - u) * (v - k))
      (mul_pos he hvk) (mul_nonneg (by linarith) he.le) (by nlinarith)
      (mul_nonneg (by linarith) hvk.le) (by ring) p (by ring) (by ring)

theorem hull_regACQ {u v k : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) :
    convexHull ℝ ({((0 : ℝ), v), (u, v + k), (u, v)} : Set (ℝ × ℝ)) = regACQ u v k := by
  have hv0 : 0 < v := by linarith
  have huk := mul_pos hu hk
  apply Set.Subset.antisymm
  · intro p hp
    have h1 := tri_le' 1 0 u (by linarith) (by linarith) (by linarith) p hp
    have h2 := tri_ge' 0 1 v (by linarith) (by linarith) (by linarith) p hp
    have h3 := tri_le' (-k) u (u * v) (by nlinarith) (by nlinarith) (by nlinarith) p hp
    exact ⟨by linarith, by linarith, by nlinarith⟩
  · rintro p ⟨h1, h2, h3⟩
    exact mem3 (u * k) ((u - p.1) * k) ((p.2 - v) * u) (k * p.1 - u * (p.2 - v))
      (mul_pos hu hk) (mul_nonneg (by linarith) hk.le) (mul_nonneg (by linarith) hu.le)
      (by nlinarith) (by ring) p (by ring) (by ring)

/-! ## (i) The union identity in frame coordinates -/

theorem frame_union {u v k e : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) (he : 0 < e) :
    regABC u v k ∪ regQ1QZ u v k e = regABQ1 u v k ∪ regAQ1Z u v k e ∪ regACQ u v k := by
  have hv0 : 0 < v := by linarith
  have hvk : 0 < v - k := by linarith
  ext p
  simp only [Set.mem_union]
  constructor
  · rintro (⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩)
    · -- a point of `ABC`
      by_cases hy : v ≤ p.2
      · exact Or.inr ⟨h1, hy, h3⟩
      · push_neg at hy
        by_cases hl : (v - k) * p.1 + u * p.2 ≤ u * v
        · exact Or.inl (Or.inl ⟨h1, h2, hl⟩)
        · push_neg at hl
          have hyk : k ≤ p.2 := by
            by_contra hc
            push_neg at hc
            nlinarith [mul_pos hu (sub_pos.2 hc), mul_nonneg hvk.le (sub_nonneg.2 h1)]
          refine Or.inl (Or.inr ⟨hy.le, hl.le, ?_⟩)
          nlinarith [mul_nonneg hvk.le (sub_nonneg.2 h1), mul_nonneg he.le (sub_nonneg.2 hyk)]
    · -- a point of `Q'QZ`
      have hyk : k ≤ p.2 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos he (sub_pos.2 hc), mul_nonneg hvk.le (sub_nonneg.2 h1)]
      refine Or.inl (Or.inr ⟨h2, ?_, h3⟩)
      nlinarith [mul_nonneg hvk.le (sub_nonneg.2 h1), mul_nonneg hu.le (sub_nonneg.2 hyk)]
  · rintro ((⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩) | ⟨h1, h2, h3⟩)
    · -- a point of `ABQ'`
      have hx : 0 ≤ p.1 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos hk (neg_pos.2 hc)]
      exact Or.inl ⟨h1, h2, by nlinarith [mul_nonneg hv0.le hx]⟩
    · -- a point of `AQ'Z`
      by_cases hx : p.1 ≤ u
      · have hx0 : 0 ≤ p.1 := by
          by_contra hc
          push_neg at hc
          nlinarith [mul_pos hvk (neg_pos.2 hc), mul_le_mul_of_nonneg_left h1 hu.le]
        exact Or.inl ⟨hx, by nlinarith [mul_nonneg hk.le hx0],
          by nlinarith [mul_nonneg hk.le hx0, mul_le_mul_of_nonneg_left h1 hu.le]⟩
      · push_neg at hx
        exact Or.inr ⟨hx.le, h1, h3⟩
    · -- a point of `ACQ`
      have hx0 : 0 ≤ p.1 := by
        by_contra hc
        push_neg at hc
        nlinarith [mul_pos hk (neg_pos.2 hc), mul_nonneg hu.le (sub_nonneg.2 h2)]
      exact Or.inl ⟨h1, by nlinarith [mul_nonneg hv0.le hx0, mul_le_mul_of_nonneg_left h2 hu.le], h3⟩

/-! ## (ii) Disjoint interiors in frame coordinates -/

/-- the base line `x = u` separates `ABC` from `Q'QZ` -/
theorem disj_ABC_Q1QZ (u v k e : ℝ) :
    Disjoint (interior (regABC u v k)) (interior (regQ1QZ u v k e)) :=
  interior_disj_fst u (fun p hp => hp.1) (fun p hp => hp.1)

/-- the cevian `AQ'` separates `ABQ'` from `AQ'Z` -/
theorem disj_ABQ1_AQ1Z {u v k : ℝ} (e : ℝ) (hvk : 0 < v - k) :
    Disjoint (interior (regABQ1 u v k)) (interior (regAQ1Z u v k e)) :=
  interior_disj_lin (v - k) u (u * v) hvk.ne' (fun p hp => hp.2.2) (fun p hp => hp.2.1)

theorem regABQ1_snd_le {u v k : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) {p : ℝ × ℝ}
    (hp : p ∈ regABQ1 u v k) : p.2 ≤ v := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hvk : 0 < v - k := by linarith
  have hx : 0 ≤ p.1 := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_pos hk (neg_pos.2 hc)]
  by_contra hc
  push_neg at hc
  nlinarith [mul_pos hu (sub_pos.2 hc), mul_nonneg hvk.le hx]

/-- the line `AQ` (`y = v`) separates `ABQ'` from `ACQ` -/
theorem disj_ABQ1_ACQ {u v k : ℝ} (hu : 0 < u) (hk : 0 < k) (hv : k < v) :
    Disjoint (interior (regABQ1 u v k)) (interior (regACQ u v k)) :=
  interior_disj_snd v (fun p hp => regABQ1_snd_le hu hk hv hp) (fun p hp => hp.2.1)

/-- the line `AQ` (`y = v`) separates `AQ'Z` from `ACQ` -/
theorem disj_AQ1Z_ACQ (u v k e : ℝ) :
    Disjoint (interior (regAQ1Z u v k e)) (interior (regACQ u v k)) :=
  interior_disj_snd v (fun p hp => hp.1) (fun p hp => hp.2.1)

/-! ## The frame parameters and the points for `F` and `t` -/

/-- `u = A0 t`, `A0 = F (F^2 - 1)`: the abscissa of the base `BC` -/
def sdU (F t : ℝ) : ℝ := F * (F ^ 2 - 1) * t
/-- `v = B0 t`, `B0 = 2 F^2 - 1`: the ordinate of the apex `A` -/
def sdV (F t : ℝ) : ℝ := (2 * F ^ 2 - 1) * t
/-- `k = F^2 t`: `|BQ'| = |CQ|` -/
def sdK (F t : ℝ) : ℝ := F ^ 2 * t
/-- `e = F t`: `|QZ|` -/
def sdE (F t : ℝ) : ℝ := F * t

/-- apex `A` of `T` -/
def ptA (F t : ℝ) : ℝ × ℝ := (0, sdV F t)
/-- base corner `B` -/
def ptB (F t : ℝ) : ℝ × ℝ := (sdU F t, 0)
/-- base corner `C` (`sdV + sdK = (3 F^2 - 1) t`) -/
def ptC (F t : ℝ) : ℝ × ℝ := (sdU F t, sdV F t + sdK F t)
/-- `Q'` on the base, `|BQ'| = F^2 t` -/
def ptQ1 (F t : ℝ) : ℝ × ℝ := (sdU F t, sdK F t)
/-- `Q` on the base, `|CQ| = F^2 t` -/
def ptQ (F t : ℝ) : ℝ × ℝ := (sdU F t, sdV F t)
/-- `Z` on the ray `AQ` beyond `Q`, `|QZ| = F t` -/
def ptZ (F t : ℝ) : ℝ × ℝ := (sdU F t + sdE F t, sdV F t)

theorem pos_facts (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    0 < sdU F t ∧ 0 < sdK F t ∧ sdK F t < sdV F t ∧ 0 < sdE F t := by
  have hF0 : 0 < F := by linarith
  have hF2 : 1 < F ^ 2 := by nlinarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold sdU; exact mul_pos (mul_pos hF0 (by linarith)) ht
  · unfold sdK; exact mul_pos (by positivity) ht
  · unfold sdK sdV; exact mul_lt_mul_of_pos_right (by linarith) ht
  · unfold sdE; exact mul_pos hF0 ht

theorem basic_pos (F : ℝ) (hF1 : 1 < F) :
    0 < F ∧ 0 < F ^ 2 - 1 ∧ 0 < 2 * F ^ 2 - 1 ∧ 0 < 3 * F ^ 2 - 1 := by
  have hF2 : 1 < F ^ 2 := by nlinarith
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-! ### Hulls of the five triangles in terms of the regions -/

theorem hull_ABC (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    convexHull ℝ ({ptA F t, ptB F t, ptC F t} : Set (ℝ × ℝ)) = regABC (sdU F t) (sdV F t) (sdK F t) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  exact hull_regABC hu hk hv

theorem hull_Q1QZ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    convexHull ℝ ({ptQ1 F t, ptQ F t, ptZ F t} : Set (ℝ × ℝ))
      = regQ1QZ (sdU F t) (sdV F t) (sdK F t) (sdE F t) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  exact hull_regQ1QZ hu hk hv he

theorem hull_ABQ1 (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    convexHull ℝ ({ptA F t, ptB F t, ptQ1 F t} : Set (ℝ × ℝ)) = regABQ1 (sdU F t) (sdV F t) (sdK F t) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  exact hull_regABQ1 hu hk hv

theorem hull_AQ1Z (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    convexHull ℝ ({ptA F t, ptQ1 F t, ptZ F t} : Set (ℝ × ℝ))
      = regAQ1Z (sdU F t) (sdV F t) (sdK F t) (sdE F t) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  exact hull_regAQ1Z hu hk hv he

theorem hull_ACQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    convexHull ℝ ({ptA F t, ptC F t, ptQ F t} : Set (ℝ × ℝ)) = regACQ (sdU F t) (sdV F t) (sdK F t) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  exact hull_regACQ hu hk hv

/-! ## (i) and (ii) in the plane -/

/-- **(i)** `T ∪ Q'QZ = ABQ' ∪ AQ'Z ∪ ACQ`, as subsets of the plane (the five triangles are the images under `Phi F`
of the convex hulls of their vertices in the skew frame). -/
theorem union_eq (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptC F t} : Set (ℝ × ℝ))
        ∪ Phi F '' convexHull ℝ ({ptQ1 F t, ptQ F t, ptZ F t} : Set (ℝ × ℝ))
      = Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptQ1 F t} : Set (ℝ × ℝ))
        ∪ Phi F '' convexHull ℝ ({ptA F t, ptQ1 F t, ptZ F t} : Set (ℝ × ℝ))
        ∪ Phi F '' convexHull ℝ ({ptA F t, ptC F t, ptQ F t} : Set (ℝ × ℝ)) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  rw [hull_ABC F t hF1 ht, hull_Q1QZ F t hF1 ht, hull_ABQ1 F t hF1 ht, hull_AQ1Z F t hF1 ht,
    hull_ACQ F t hF1 ht]
  simp only [← Set.image_union]
  rw [frame_union hu hk hv he]

/-- **(ii)** the base line `x = A0 t` separates `T = ABC` from `Q'QZ`. -/
theorem disjoint_ABC_Q1QZ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    Disjoint (interior (Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptC F t} : Set (ℝ × ℝ))))
      (interior (Phi F '' convexHull ℝ ({ptQ1 F t, ptQ F t, ptZ F t} : Set (ℝ × ℝ)))) := by
  rw [hull_ABC F t hF1 ht, hull_Q1QZ F t hF1 ht]
  exact disjoint_image hF1 (disj_ABC_Q1QZ _ _ _ _)

/-- **(ii)** the cevian `AQ'` separates `ABQ'` from `AQ'Z`. -/
theorem disjoint_ABQ1_AQ1Z (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    Disjoint (interior (Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptQ1 F t} : Set (ℝ × ℝ))))
      (interior (Phi F '' convexHull ℝ ({ptA F t, ptQ1 F t, ptZ F t} : Set (ℝ × ℝ)))) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  rw [hull_ABQ1 F t hF1 ht, hull_AQ1Z F t hF1 ht]
  exact disjoint_image hF1 (disj_ABQ1_AQ1Z _ (by linarith))

/-- **(ii)** the line `AQ` separates `ABQ'` from `ACQ`. -/
theorem disjoint_ABQ1_ACQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    Disjoint (interior (Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptQ1 F t} : Set (ℝ × ℝ))))
      (interior (Phi F '' convexHull ℝ ({ptA F t, ptC F t, ptQ F t} : Set (ℝ × ℝ)))) := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  rw [hull_ABQ1 F t hF1 ht, hull_ACQ F t hF1 ht]
  exact disjoint_image hF1 (disj_ABQ1_ACQ hu hk hv)

/-- **(ii)** the line `AQ` separates `AQ'Z` from `ACQ`. -/
theorem disjoint_AQ1Z_ACQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    Disjoint (interior (Phi F '' convexHull ℝ ({ptA F t, ptQ1 F t, ptZ F t} : Set (ℝ × ℝ))))
      (interior (Phi F '' convexHull ℝ ({ptA F t, ptC F t, ptQ F t} : Set (ℝ × ℝ)))) := by
  rw [hull_AQ1Z F t hF1 ht, hull_ACQ F t hF1 ht]
  exact disjoint_image hF1 (disj_AQ1Z_ACQ _ _ _ _)

/-! ## (iii) Side lengths -/

theorem dist_Phi_eq (F : ℝ) (hF1 : 1 < F) (p q : ℝ × ℝ) (d : ℝ) (hd : 0 ≤ d)
    (h : (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 + (p.1 - q.1) * (p.2 - q.2) / F = d ^ 2) :
    dist (Phi F p) (Phi F q) = d := by
  refine (sq_eq_sq₀ dist_nonneg hd).mp ?_
  rw [sq_Phi hF1]
  exact h

/-- `|AB| = F^3 t` (a leg of `T`) -/
theorem d_AB (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptA F t)) (Phi F (ptB F t)) = F ^ 3 * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (pow_pos hFp 3) ht).le ?_
  simp only [ptA, ptB, sdU, sdV]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|AC| = F^3 t` (the other leg of `T`) -/
theorem d_AC (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptA F t)) (Phi F (ptC F t)) = F ^ 3 * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (pow_pos hFp 3) ht).le ?_
  simp only [ptA, ptC, sdU, sdV, sdK]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|BC| = (3 F^2 - 1) t` (the base of `T`) -/
theorem d_BC (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptB F t)) (Phi F (ptC F t)) = (3 * F ^ 2 - 1) * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos hC ht).le ?_
  simp only [ptB, ptC, sdU, sdV, sdK]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|BQ'| = F^2 t` -/
theorem d_BQ1 (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptB F t)) (Phi F (ptQ1 F t)) = F ^ 2 * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (pow_pos hFp 2) ht).le ?_
  simp only [ptB, ptQ1, sdU, sdK]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|CQ| = F^2 t` -/
theorem d_CQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptC F t)) (Phi F (ptQ F t)) = F ^ 2 * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (pow_pos hFp 2) ht).le ?_
  simp only [ptC, ptQ, sdU, sdV, sdK]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|AQ'| = F (F^2 - 1) t` (the cevian) -/
theorem d_AQ1 (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptA F t)) (Phi F (ptQ1 F t)) = F * (F ^ 2 - 1) * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (mul_pos hFp hA) ht).le ?_
  simp only [ptA, ptQ1, sdU, sdV, sdK]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|AQ| = F (F^2 - 1) t` (the cevian) -/
theorem d_AQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptA F t)) (Phi F (ptQ F t)) = F * (F ^ 2 - 1) * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (mul_pos hFp hA) ht).le ?_
  simp only [ptA, ptQ, sdU, sdV]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|AZ| = F^3 t` -/
theorem d_AZ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptA F t)) (Phi F (ptZ F t)) = F ^ 3 * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (pow_pos hFp 3) ht).le ?_
  simp only [ptA, ptZ, sdU, sdV, sdE]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|Q'Z| = F^2 t` -/
theorem d_Q1Z (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptQ1 F t)) (Phi F (ptZ F t)) = F ^ 2 * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos (pow_pos hFp 2) ht).le ?_
  simp only [ptQ1, ptZ, sdU, sdV, sdK, sdE]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|Q'Q| = (F^2 - 1) t` -/
theorem d_Q1Q (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptQ1 F t)) (Phi F (ptQ F t)) = (F ^ 2 - 1) * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos hA ht).le ?_
  simp only [ptQ1, ptQ, sdU, sdV, sdK]
  first | ring1 | (field_simp; ring1) | field_simp

/-- `|QZ| = F t` -/
theorem d_QZ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    dist (Phi F (ptQ F t)) (Phi F (ptZ F t)) = F * t := by
  obtain ⟨hFp, hA, hB, hC⟩ := basic_pos F hF1
  have hF0 : F ≠ 0 := hFp.ne'
  refine dist_Phi_eq F hF1 _ _ _ (mul_pos hFp ht).le ?_
  simp only [ptQ, ptZ, sdU, sdV, sdE]
  first | ring1 | (field_simp; ring1) | field_simp

/-! ### The five triangles as `Tri`s (`triC`) -/

theorem nd_ABC (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    ((ptB F t).1 - (ptA F t).1) * ((ptC F t).2 - (ptA F t).2) -
      ((ptC F t).1 - (ptA F t).1) * ((ptB F t).2 - (ptA F t).2) ≠ 0 := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  have e : ((ptB F t).1 - (ptA F t).1) * ((ptC F t).2 - (ptA F t).2) -
      ((ptC F t).1 - (ptA F t).1) * ((ptB F t).2 - (ptA F t).2) = sdU F t * (sdV F t + sdK F t) := by
    simp only [ptA, ptB, ptC]; ring
  rw [e]
  exact (mul_pos hu (by linarith)).ne'

theorem nd_ABQ1 (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    ((ptB F t).1 - (ptA F t).1) * ((ptQ1 F t).2 - (ptA F t).2) -
      ((ptQ1 F t).1 - (ptA F t).1) * ((ptB F t).2 - (ptA F t).2) ≠ 0 := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  have e : ((ptB F t).1 - (ptA F t).1) * ((ptQ1 F t).2 - (ptA F t).2) -
      ((ptQ1 F t).1 - (ptA F t).1) * ((ptB F t).2 - (ptA F t).2) = sdU F t * sdK F t := by
    simp only [ptA, ptB, ptQ1]; ring
  rw [e]
  exact (mul_pos hu hk).ne'

theorem nd_AQ1Z (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    ((ptQ1 F t).1 - (ptA F t).1) * ((ptZ F t).2 - (ptA F t).2) -
      ((ptZ F t).1 - (ptA F t).1) * ((ptQ1 F t).2 - (ptA F t).2) ≠ 0 := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  have e : ((ptQ1 F t).1 - (ptA F t).1) * ((ptZ F t).2 - (ptA F t).2) -
      ((ptZ F t).1 - (ptA F t).1) * ((ptQ1 F t).2 - (ptA F t).2)
      = (sdU F t + sdE F t) * (sdV F t - sdK F t) := by
    simp only [ptA, ptQ1, ptZ]; ring
  rw [e]
  exact (mul_pos (by linarith) (by linarith)).ne'

theorem nd_Q1QZ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    ((ptQ F t).1 - (ptQ1 F t).1) * ((ptZ F t).2 - (ptQ1 F t).2) -
      ((ptZ F t).1 - (ptQ1 F t).1) * ((ptQ F t).2 - (ptQ1 F t).2) ≠ 0 := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  have e : ((ptQ F t).1 - (ptQ1 F t).1) * ((ptZ F t).2 - (ptQ1 F t).2) -
      ((ptZ F t).1 - (ptQ1 F t).1) * ((ptQ F t).2 - (ptQ1 F t).2)
      = -(sdE F t * (sdV F t - sdK F t)) := by
    simp only [ptQ1, ptQ, ptZ]; ring
  rw [e]
  exact neg_ne_zero.2 (mul_pos he (by linarith)).ne'

theorem nd_ACQ (F t : ℝ) (hF1 : 1 < F) (ht : 0 < t) :
    ((ptC F t).1 - (ptA F t).1) * ((ptQ F t).2 - (ptA F t).2) -
      ((ptQ F t).1 - (ptA F t).1) * ((ptC F t).2 - (ptA F t).2) ≠ 0 := by
  obtain ⟨hu, hk, hv, he⟩ := pos_facts F t hF1 ht
  have e : ((ptC F t).1 - (ptA F t).1) * ((ptQ F t).2 - (ptA F t).2) -
      ((ptQ F t).1 - (ptA F t).1) * ((ptC F t).2 - (ptA F t).2) = -(sdU F t * sdK F t) := by
    simp only [ptA, ptC, ptQ]; ring
  rw [e]
  exact neg_ne_zero.2 (mul_pos hu hk).ne'

/-- `T = ABC` (vertices in the order `A, B, C`) -/
noncomputable def triABC (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Erdos634.Geometry.Tri :=
  triC F hF1 (ptA F t) (ptB F t) (ptC F t) (nd_ABC F t hF1 ht)

/-- `Q'QZ` (vertices in the order `Q', Q, Z`) -/
noncomputable def triQ1QZ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Erdos634.Geometry.Tri :=
  triC F hF1 (ptQ1 F t) (ptQ F t) (ptZ F t) (nd_Q1QZ F t hF1 ht)

/-- `ABQ'` (vertices in the order `A, B, Q'`) -/
noncomputable def triABQ1 (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Erdos634.Geometry.Tri :=
  triC F hF1 (ptA F t) (ptB F t) (ptQ1 F t) (nd_ABQ1 F t hF1 ht)

/-- `AQ'Z` (vertices in the order `A, Q', Z`) -/
noncomputable def triAQ1Z (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Erdos634.Geometry.Tri :=
  triC F hF1 (ptA F t) (ptQ1 F t) (ptZ F t) (nd_AQ1Z F t hF1 ht)

/-- `ACQ` (vertices in the order `A, C, Q`) -/
noncomputable def triACQ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Erdos634.Geometry.Tri :=
  triC F hF1 (ptA F t) (ptC F t) (ptQ F t) (nd_ACQ F t hF1 ht)

theorem carrier_triABC (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    (triABC F hF1 t ht).carrier = Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptC F t} : Set (ℝ × ℝ)) :=
  carrier_triC F hF1 _ _ _ _

theorem carrier_triQ1QZ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    (triQ1QZ F hF1 t ht).carrier
      = Phi F '' convexHull ℝ ({ptQ1 F t, ptQ F t, ptZ F t} : Set (ℝ × ℝ)) :=
  carrier_triC F hF1 _ _ _ _

theorem carrier_triABQ1 (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    (triABQ1 F hF1 t ht).carrier
      = Phi F '' convexHull ℝ ({ptA F t, ptB F t, ptQ1 F t} : Set (ℝ × ℝ)) :=
  carrier_triC F hF1 _ _ _ _

theorem carrier_triAQ1Z (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    (triAQ1Z F hF1 t ht).carrier
      = Phi F '' convexHull ℝ ({ptA F t, ptQ1 F t, ptZ F t} : Set (ℝ × ℝ)) :=
  carrier_triC F hF1 _ _ _ _

theorem carrier_triACQ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    (triACQ F hF1 t ht).carrier = Phi F '' convexHull ℝ ({ptA F t, ptC F t, ptQ F t} : Set (ℝ × ℝ)) :=
  carrier_triC F hF1 _ _ _ _

/-- the sides of `triC a b c` opposite its vertices `0, 1, 2` are `|bc|, |ca|, |ab|` -/
theorem hasSides_triC (F : ℝ) (hF1 : 1 < F) (a b c : ℝ × ℝ) (h) (x y z : ℝ)
    (h12 : dist (Phi F b) (Phi F c) = x) (h20 : dist (Phi F c) (Phi F a) = y)
    (h01 : dist (Phi F a) (Phi F b) = z) : HasSides (triC F hF1 a b c h) x y z := by
  refine ⟨Equiv.refl _, ?_, ?_, ?_⟩
  · simp only [Equiv.refl_apply, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact h12
  · simp only [Equiv.refl_apply, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact h20
  · simp only [Equiv.refl_apply, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    exact h01

theorem hasSides_eq {T : Erdos634.Geometry.Tri} {a b c a' b' c' : ℝ} (h : HasSides T a b c) (ha : a = a') (hb : b = b')
    (hc : c = c') : HasSides T a' b' c' := by
  subst ha hb hc
  exact h

/-- **(iii)** `T = ABC` has the sides `F^3 t`, `F^3 t`, `(3 F^2 - 1) t` (legs `M f^3`, base `M (3 f^2 - 1)`). -/
theorem sides_ABC (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    HasSides (triABC F hF1 t ht) (F ^ 3 * t) (F ^ 3 * t) ((3 * F ^ 2 - 1) * t) := by
  have base : HasSides (triABC F hF1 t ht) ((3 * F ^ 2 - 1) * t) (F ^ 3 * t) (F ^ 3 * t) :=
    hasSides_triC F hF1 (ptA F t) (ptB F t) (ptC F t) (nd_ABC F t hF1 ht) _ _ _
      (d_BC F t hF1 ht) ((dist_comm _ _).trans (d_AC F t hF1 ht)) (d_AB F t hF1 ht)
  exact hasSides_rot base

/-- **(iii)** `Q'QZ` has the sides `t F`, `t F^2`, `t (F^2 - 1)`: it is the tile `(f, f^2, f^2 - 1)` at scale `t`. -/
theorem sides_Q1QZ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    HasSides (triQ1QZ F hF1 t ht) (t * F) (t * F ^ 2) (t * (F ^ 2 - 1)) := by
  have base : HasSides (triQ1QZ F hF1 t ht) (F * t) (F ^ 2 * t) ((F ^ 2 - 1) * t) :=
    hasSides_triC F hF1 (ptQ1 F t) (ptQ F t) (ptZ F t) (nd_Q1QZ F t hF1 ht) _ _ _
      (d_QZ F t hF1 ht) ((dist_comm _ _).trans (d_Q1Z F t hF1 ht)) (d_Q1Q F t hF1 ht)
  exact hasSides_eq base (by ring) (by ring) (by ring)

/-- **(iii)** `ABQ'` has the sides `t F * F`, `t F * F^2`, `t F * (F^2 - 1)`: the tile at scale `t F`. -/
theorem sides_ABQ1 (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    HasSides (triABQ1 F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1)) := by
  have base : HasSides (triABQ1 F hF1 t ht) (F ^ 2 * t) (F * (F ^ 2 - 1) * t) (F ^ 3 * t) :=
    hasSides_triC F hF1 (ptA F t) (ptB F t) (ptQ1 F t) (nd_ABQ1 F t hF1 ht) _ _ _
      (d_BQ1 F t hF1 ht) ((dist_comm _ _).trans (d_AQ1 F t hF1 ht)) (d_AB F t hF1 ht)
  exact hasSides_eq (hasSides_rot (hasSides_swap base)) (by ring) (by ring) (by ring)

/-- **(iii)** `AQ'Z` has the sides `t F * F`, `t F * F^2`, `t F * (F^2 - 1)`: the tile at scale `t F`. -/
theorem sides_AQ1Z (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    HasSides (triAQ1Z F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1)) := by
  have base : HasSides (triAQ1Z F hF1 t ht) (F ^ 2 * t) (F ^ 3 * t) (F * (F ^ 2 - 1) * t) :=
    hasSides_triC F hF1 (ptA F t) (ptQ1 F t) (ptZ F t) (nd_AQ1Z F t hF1 ht) _ _ _
      (d_Q1Z F t hF1 ht) ((dist_comm _ _).trans (d_AZ F t hF1 ht)) (d_AQ1 F t hF1 ht)
  exact hasSides_eq base (by ring) (by ring) (by ring)

/-- **(iii)** `ACQ` has the sides `t F * F`, `t F * F^2`, `t F * (F^2 - 1)`: the tile at scale `t F`. -/
theorem sides_ACQ (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    HasSides (triACQ F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1)) := by
  have base : HasSides (triACQ F hF1 t ht) (F ^ 2 * t) (F * (F ^ 2 - 1) * t) (F ^ 3 * t) :=
    hasSides_triC F hF1 (ptA F t) (ptC F t) (ptQ F t) (nd_ACQ F t hF1 ht) _ _ _
      (d_CQ F t hF1 ht) ((dist_comm _ _).trans (d_AQ F t hF1 ht)) (d_AC F t hF1 ht)
  exact hasSides_eq (hasSides_rot (hasSides_swap base)) (by ring) (by ring) (by ring)

/-! ## The decomposition -/

/-- The signed decomposition at the real parameters `F > 1`, `t > 0` (carriers of the five `triC` triangles):
the union identity, the four disjointness statements, and the side lengths. -/
def SignedDecomp (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) : Prop :=
  ((triABC F hF1 t ht).carrier ∪ (triQ1QZ F hF1 t ht).carrier =
      (triABQ1 F hF1 t ht).carrier ∪ (triAQ1Z F hF1 t ht).carrier ∪ (triACQ F hF1 t ht).carrier) ∧
    Disjoint (interior (triABC F hF1 t ht).carrier) (interior (triQ1QZ F hF1 t ht).carrier) ∧
    Disjoint (interior (triABQ1 F hF1 t ht).carrier) (interior (triAQ1Z F hF1 t ht).carrier) ∧
    Disjoint (interior (triABQ1 F hF1 t ht).carrier) (interior (triACQ F hF1 t ht).carrier) ∧
    Disjoint (interior (triAQ1Z F hF1 t ht).carrier) (interior (triACQ F hF1 t ht).carrier) ∧
    HasSides (triABC F hF1 t ht) (F ^ 3 * t) (F ^ 3 * t) ((3 * F ^ 2 - 1) * t) ∧
    HasSides (triQ1QZ F hF1 t ht) (t * F) (t * F ^ 2) (t * (F ^ 2 - 1)) ∧
    HasSides (triABQ1 F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1)) ∧
    HasSides (triAQ1Z F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1)) ∧
    HasSides (triACQ F hF1 t ht) (t * F * F) (t * F * F ^ 2) (t * F * (F ^ 2 - 1))

theorem signed_decomposition_real (F : ℝ) (hF1 : 1 < F) (t : ℝ) (ht : 0 < t) :
    SignedDecomp F hF1 t ht := by
  unfold SignedDecomp
  refine ⟨?_, ?_, ?_, ?_, ?_, sides_ABC F hF1 t ht, sides_Q1QZ F hF1 t ht, sides_ABQ1 F hF1 t ht,
    sides_AQ1Z F hF1 t ht, sides_ACQ F hF1 t ht⟩
  · rw [carrier_triABC, carrier_triQ1QZ, carrier_triABQ1, carrier_triAQ1Z, carrier_triACQ]
    exact union_eq F t hF1 ht
  · rw [carrier_triABC, carrier_triQ1QZ]
    exact disjoint_ABC_Q1QZ F t hF1 ht
  · rw [carrier_triABQ1, carrier_triAQ1Z]
    exact disjoint_ABQ1_AQ1Z F t hF1 ht
  · rw [carrier_triABQ1, carrier_triACQ]
    exact disjoint_ABQ1_ACQ F t hF1 ht
  · rw [carrier_triAQ1Z, carrier_triACQ]
    exact disjoint_AQ1Z_ACQ F t hF1 ht

theorem natpos {M : ℕ} (hM : 1 ≤ M) : (0 : ℝ) < M :=
  Nat.cast_pos.mpr (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)

/-- the carrier of `triABC` at `F = f`, `t = M` is the carrier of the frame triangle `WtoDeltaF.DeltaTri` of `T_M` -/
theorem carrier_triABC_eq_DeltaTri (f M : ℕ) (hf : 2 ≤ f) (hM : 1 ≤ M) :
    (triABC (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) (M : ℝ) (natpos hM)).carrier
      = (DeltaTri f hf M (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)).carrier := by
  have key : regABC (sdU (f : ℝ) (M : ℝ)) (sdV (f : ℝ) (M : ℝ)) (sdK (f : ℝ) (M : ℝ))
      = DS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * M) ((2 * (f : ℝ) ^ 2 - 1) * M) ((3 * (f : ℝ) ^ 2 - 1) * M) := by
    ext p
    simp only [regABC, DS, Set.mem_setOf_eq, sdU, sdV, sdK]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by nlinarith [h3]⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, h2, by nlinarith [h3]⟩
  rw [carrier_triABC, carrier_DeltaTri, hull_ABC _ _ (Erdos634.Draft.WPgramF.hF f hf) (natpos hM)]
  exact congrArg (fun S => Phi (f : ℝ) '' S) key

/-- **The signed decomposition of the member `(1, f)` at the scale `M`** (paper, Proposition `prop:reframe`(a), which
reads: "Let `f ≥ 2` and `M ≥ 1`, `(a, b, c) = (f, f^2 - 1, f^2)`, and let `T_M = ABC` be the isosceles triangle with apex
`A` of angle `3α`, legs `M f^3` and base `BC = M (3 f^2 - 1)`.  Let `Q', Q` be the points of the base with
`|BQ'| = |CQ| = M f^2` ... Let `Z` be the point of the ray `AQ` beyond `Q` with `|QZ| = M f`.  Then `ABQ'`, `ACQ` and
`AQ'Z` are copies of the tile at scale `f M`, `Q'QZ` is a copy of the tile at scale `M` lying on the other side of the
base, and `T_M ∪ Q'QZ = ABQ' ∪ AQ'Z ∪ ACQ` with disjoint interiors on each side.")

Formal content, for `F = f`, `t = M` in the skew frame `Phi_f` of `WFrameF`: the union identity of the carriers of the five
triangles (`ABC`, `Q'QZ`, `ABQ'`, `AQ'Z`, `ACQ`), the pairwise disjointness of the interiors on each side (`T` against
`Q'QZ`; the three pairs among `ABQ'`, `AQ'Z`, `ACQ`), and their side lengths through `HasSides`: `T` has `M f^3`, `M f^3`,
`(3 f^2 - 1) M`; `ABQ'`, `AQ'Z`, `ACQ` have the sides `M f * f`, `M f * f^2`, `M f * (f^2 - 1)` (the tile `(f, f^2, f^2 - 1)`
at scale `M f`); `Q'QZ` has `M f`, `M f^2`, `M (f^2 - 1)` (the tile at scale `M`).  Also, the carrier of `T = triABC` is
the carrier of `WtoDeltaF.DeltaTri f hf M`.  (Congruence of a triangle with the scaled tile is `FDBBaseBetaE1.congruent_of_hasSides`
from these side lengths.) -/
theorem signed_decomposition (f M : ℕ) (hf : 2 ≤ f) (hM : 1 ≤ M) :
    SignedDecomp (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) (M : ℝ) (natpos hM) ∧
      (triABC (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf) (M : ℝ) (natpos hM)).carrier
        = (DeltaTri f hf M (Nat.lt_of_lt_of_le Nat.zero_lt_one hM)).carrier :=
  ⟨signed_decomposition_real _ _ _ _, carrier_triABC_eq_DeltaTri f M hf hM⟩

end Erdos634.Draft.SignedDecompE1

#print axioms Erdos634.Draft.SignedDecompE1.frame_union
#print axioms Erdos634.Draft.SignedDecompE1.union_eq
#print axioms Erdos634.Draft.SignedDecompE1.disjoint_ABC_Q1QZ
#print axioms Erdos634.Draft.SignedDecompE1.disjoint_ABQ1_AQ1Z
#print axioms Erdos634.Draft.SignedDecompE1.disjoint_ABQ1_ACQ
#print axioms Erdos634.Draft.SignedDecompE1.disjoint_AQ1Z_ACQ
#print axioms Erdos634.Draft.SignedDecompE1.d_AB
#print axioms Erdos634.Draft.SignedDecompE1.d_Q1Z
#print axioms Erdos634.Draft.SignedDecompE1.sides_ABC
#print axioms Erdos634.Draft.SignedDecompE1.sides_ABQ1
#print axioms Erdos634.Draft.SignedDecompE1.signed_decomposition_real
#print axioms Erdos634.Draft.SignedDecompE1.signed_decomposition
