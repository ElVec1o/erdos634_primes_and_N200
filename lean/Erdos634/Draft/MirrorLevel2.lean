-- Draft/MirrorLevel2.lean — R6:
-- the ARITHMETIC of the level-2 mirror kill (M)₂ and the
-- lattice coordinates `Λ(i,k)` of the two strips.  Everything here is proved (no `sorry`).
-- Imported by All.lean.
--
-- Tile `(a,b,c) = (ef, b, f²)`, `b + e² = f²` (the `Inflation` convention); `InS` as in
-- Draft/HalfTurnR3R4.  Coordinates as Draft/MirrorStripR2 §2 (apex at the origin, axis down,
-- `sin x = e/(2f)`, `x = α/2`).
--
-- Every arithmetic step of R6 is available in other modules; this file restates
-- each in R6's gap form and cites:
--   * `kc − b ∉ S`, `1 ≤ k ≤ f−1` (Lemma A on L₂)      = `Inflation.c_side_no_b`.
--     (`HalfTurnR3R4.chain_point_minus_b_not_mem` is the weaker `kc < fb` form.)
--   * the end step "(f−2)c with a b"                  = `Inflation.c_side_no_b` at `k = f − 2`.
--   * `a − b ∉ S` (S1's twisted fill (ii))            = `Inflation.a_side_no_b` at `k = 1`
--     (and `ThickEFminus1Probe.leftover_a_sub_b_nonrep` at `e = f−1`, `ThickEFminus1Steps.a_rep_unique`).
--     No hypothesis `gcd(a,b) = 1, b ≥ 5` is needed.  Stated additively (`w + b ≠ a`), so the
--     `a < b` case (where ℕ-subtraction would give `0 ∈ S`) is covered.
--   * `2a = a + a` only, `f ≥ 3` (2a-rigidity)         = `HalfTurnR3R4.two_a_rigid`
--                                                      = `Inflation.a_side_no_b` + `a_side_rigid`.
--   * `2a − c ∉ S`                                     = `HalfTurnR3R4.two_a_ne_c_add` (additive form),
--                                                        `two_a_sub_c_not_mem` / `m2_step_dichotomy`.
--   * `e² = c − b ∉ S` (k = 1)                          = `c_side_no_b` at `k = 1`.
-- New here: the lattice
-- coordinates `Λ(i,k) = i·P′ + J_k`, `Λ(i,k) = J_{i+k} + (i·a, 0)`, the base criterion `i + k = f`, and
-- `|Λ(2,0) Λ(2,f−2)| = (f−2)·c` (L₂'s length), two-line consequences of `MirrorStripR2.apex_offsets`.
import Erdos634.Draft.HalfTurnR3R4
import Erdos634.Draft.MirrorStripR2

namespace Erdos634.Draft.MirrorLevel2

open Erdos634.Draft.HalfTurnR3R4

/-! ## §1 Arithmetic of (M)₂ (all corpus citations) -/

/-- **Lemma A on L₂ (R6 step (a) and End), gap form.**  For `1 ≤ k ≤ f − 1`, no word `w ∈ S`
has `w + b = k·c`: a band side of `L₂` of value `k·c` that starts with `N₂`'s `b` is impossible.
Corpus: `Inflation.c_side_no_b`. -/
theorem kc_sub_b_not_mem {e f b k na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) (hk : k < f) :
    na * (e * f) + nb * b + nc * f ^ 2 + b ≠ k * f ^ 2 := by
  intro h
  have := Inflation.c_side_no_b e f b k na (nb + 1) nc he hef hcop hb hk (by rw [← h]; ring)
  omega

/-- The same, as `¬ InS (k·c − b)` (with `b ≤ k·c`, so ℕ-subtraction is honest). -/
theorem kc_sub_b_not_InS {e f b k : ℕ} (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hk : k < f) (hbk : b ≤ k * f ^ 2) : ¬ InS e f b (k * f ^ 2 - b) := by
  rintro ⟨na, nb, nc, h⟩
  exact kc_sub_b_not_mem (na := na) (nb := nb) (nc := nc) he hef hcop hb hk (by omega)

/-- **R6 End step.**  `L₂`'s band side totals `(f−2)·c` and starts with `b`: impossible (`f ≥ 2`).
This is `c_side_no_b` at `k = f − 2`. -/
theorem end_step {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hnb : 1 ≤ nb)
    (h : na * (e * f) + nb * b + nc * f ^ 2 = (f - 2) * f ^ 2) : False := by
  have := Inflation.c_side_no_b e f b (f - 2) na nb nc he hef hcop hb (by omega) h
  omega

/-- `e² = c − b ∉ S` (the `k = 1` case of `kc_sub_b_not_mem`, since `c − b = e²`). -/
theorem e_sq_not_InS {e f b : ℕ} (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2) : ¬ InS e f b (e ^ 2) := by
  rintro ⟨na, nb, nc, h⟩
  exact kc_sub_b_not_mem (k := 1) (na := na) (nb := nb) (nc := nc) he hef hcop hb (by omega)
    (by rw [h]; omega)

/-- **`a − b ∉ S` (S1: the twisted fill (ii) is dead at every member), additive form.**  No `w ∈ S`
has `w + b = a`; for `a < b` this is trivial, for `a > b` it is `a − b ∉ S`.  Corpus:
`Inflation.a_side_no_b` at `k = 1` (a representation of `a` carries no `b`). -/
theorem a_sub_b_not_mem {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2) : na * (e * f) + nb * b + nc * f ^ 2 + b ≠ e * f := by
  intro h
  have := Inflation.a_side_no_b e f b 1 na (nb + 1) nc he hef hcop hb (by omega)
    (by rw [one_mul, add_mul, one_mul]; omega)
  omega

/-- `a − b ∉ S` as `¬ InS`, in the case `b < a` where it is a genuine positive gap. -/
theorem a_sub_b_not_InS {e f b : ℕ} (he : 1 ≤ e) (hef : e < f) (hcop : Nat.Coprime e f)
    (hb : b + e ^ 2 = f ^ 2) (hba : b ≤ e * f) : ¬ InS e f b (e * f - b) := by
  rintro ⟨na, nb, nc, h⟩
  exact a_sub_b_not_mem (na := na) (nb := nb) (nc := nc) he hef hcop hb (by omega)

/-- **2a-rigidity (R6 steps (b), (d)):** `2a` has only `a + a` (`f ≥ 3`).  Corpus:
`HalfTurnR3R4.two_a_rigid` (= `Inflation.a_side_no_b` + `a_side_rigid`). -/
theorem two_a_only {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f) (hf3 : 3 ≤ f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2)
    (h : na * (e * f) + nb * b + nc * f ^ 2 = 2 * (e * f)) : na = 2 ∧ nb = 0 ∧ nc = 0 :=
  two_a_rigid he hef hf3 hcop hb h

/-- **`2a − c ∉ S`, additive form** (`w + c ≠ 2a`, `f ≥ 3`).  Corpus: `HalfTurnR3R4.two_a_ne_c_add`. -/
theorem two_a_sub_c_not_mem' {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f) (hf3 : 3 ≤ f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) :
    na * (e * f) + nb * b + nc * f ^ 2 + f ^ 2 ≠ 2 * (e * f) :=
  two_a_ne_c_add he hef hf3 hcop hb

/-- **A row segment of length `2a` whose first edge is `b` is impossible** (`w + b ≠ 2a`, `f ≥ 3`):
the lower side of each row segment `[Q^L_k + P′, J_{k+2}]` is `a + a` (steps (b), (d)). -/
theorem two_a_sub_b_not_mem {e f b na nb nc : ℕ} (he : 1 ≤ e) (hef : e < f) (hf3 : 3 ≤ f)
    (hcop : Nat.Coprime e f) (hb : b + e ^ 2 = f ^ 2) :
    na * (e * f) + nb * b + nc * f ^ 2 + b ≠ 2 * (e * f) := by
  intro h
  have := (two_a_rigid (na := na) (nb := nb + 1) (nc := nc) he hef hf3 hcop hb
    (by rw [← h]; ring)).2.1
  omega

/-! ### Witnesses (vacuity rule) and necessity of `m = 1` -/

/-- The hypotheses are satisfiable: `(e,f,b) = (4,7,33)` (`N = 131`) is coprime with `b + e² = f²`,
`f ≥ 3`; `k = f − 2 = 5 < f`; `b < a` fails and `a < b` holds there, `(7,10,51)` has `b < a`. -/
theorem r6_hyps_satisfiable :
    Nat.Coprime 4 7 ∧ 33 + 4 ^ 2 = 7 ^ 2 ∧ 3 ≤ 7 ∧ 7 - 2 < 7 ∧ 4 * 7 < 33 ∧
    Nat.Coprime 7 10 ∧ 51 + 7 ^ 2 = 10 ^ 2 ∧ 51 ≤ 7 * 10 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num⟩

/-- The `m = 1` steps fail at `N = 44` (`(e,f,b) = (1,2,3)`, tile `(2,3,4)`), exactly where the review
says: `2c − b = 5 = a + b ∈ S` (`k = 2 = f`, outside Lemma A's range), `2a = c`. -/
theorem r6_fails_N44 : InS 1 2 3 (2 * 2 ^ 2 - 3) ∧ 2 * (1 * 2) = 2 ^ 2 :=
  ⟨⟨1, 1, 0, by norm_num⟩, by norm_num⟩

/-- Lemma A's range is sharp: at `k = f` the `c`-side word `(e, f, 0)` carries `f` `b`-edges
(`Inflation.c_side_b_word_at_f`, cited), so `k < f` in `kc_sub_b_not_mem` cannot be dropped. -/
theorem kc_sub_b_sharp_at_f (e f b : ℕ) (hef : e ≤ f) (hb : b + e ^ 2 = f ^ 2) :
    e * (e * f) + f * b + 0 * f ^ 2 = f * f ^ 2 :=
  Inflation.c_side_b_word_at_f e f b hef hb

/-! ## §2 The lattice `Λ(i,k)` and the row line `L₂` (real, MirrorStripR2 coordinates) -/

open Real Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.MirrorStripR2

/-- `Λ(i,k) = i·P′ + J_k` (apex at the origin).  Row `i + k`; `Λ(1,0) = P′`, `Λ(2,0) = 2P′`,
`Λ(0,k) = J_k`, `Λ(1,k) = Q^L_k`, `Λ(2,k) = Q^L_k + P′`. -/
noncomputable def lam (e f x i k : ℝ) : Plane :=
  mkPt (i * (pP e f x) 0 + (pJ f x k) 0) (i * (pP e f x) 1 + (pJ f x k) 1)

/-- **Closed form.**  `Λ(i,k) = (−(e/2f)(i·b + k(3f² − e²)), −(i+k)·b·cos x)`, and
`b·cos x = ρ = b√(4f²−e²)/(2f)` is the row height. -/
theorem lam_closed {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) (i k : ℝ) :
    lam e f x i k = mkPt (-(e / (2 * f)) * (i * (f ^ 2 - e ^ 2) + k * (3 * f ^ 2 - e ^ 2)))
      (-(i + k) * ((f ^ 2 - e ^ 2) * cos x)) := by
  obtain ⟨h1, h2⟩ := apex_offsets hf hs
  have ht : e / (2 * f) * (2 * f) = e := by field_simp
  unfold lam pP pJ
  simp only [mkPt_zero, mkPt_one]
  congr 1
  · linear_combination (-k) * h1 + (-(i + k) * (f ^ 2 - e ^ 2)) * hs + (k * f) * ht
  · linear_combination (-k) * h2

/-- **Horizontal offset.**  `Λ(i,k) = J_{i+k} + (i·a, 0)`: the lattice point sits on row `i + k`,
horizontally `i·a` right of the left leg (`a = ef`). -/
theorem lam_eq_J_add {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) (i k : ℝ) :
    lam e f x i k = mkPt ((pJ f x (i + k)) 0 + i * (e * f)) ((pJ f x (i + k)) 1) := by
  obtain ⟨h1, h2⟩ := apex_offsets hf hs
  unfold lam pP pJ
  simp only [mkPt_zero, mkPt_one]
  congr 1
  · linear_combination i * h1
  · linear_combination i * h2

/-- **On the base iff `i + k = f`.**  `Λ(i,k)` has the base's depth (that of the base corner `J_f`)
exactly when `i + k = f` (needs `b·cos x ≠ 0`, i.e. `e < f`, `cos x > 0`). -/
theorem lam_on_base_iff {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (hcos : 0 < cos x) (i k : ℝ) : (lam e f x i k) 1 = (pJ f x f) 1 ↔ i + k = f := by
  have hf : 0 < f := he.trans hef
  obtain ⟨-, h2⟩ := apex_offsets hf.ne' hs
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hbc : 0 < (f ^ 2 - e ^ 2) * cos x := mul_pos hb hcos
  unfold lam pP pJ
  simp only [mkPt_one]
  constructor
  · intro h
    have h' : (i + k - f) * ((f ^ 2 - e ^ 2) * cos x) = 0 := by linear_combination -h + (f - k) * h2
    rcases mul_eq_zero.mp h' with h0 | h0
    · linarith
    · linarith
  · intro h
    have hk : k = f - i := by linarith
    subst hk
    linear_combination i * h2

/-- **`L₂` has length `(f−2)·c`.**  `L₂` is the line through `2P′ = Λ(2,0)` parallel to the leg; it
meets the base at `Λ(2, f−2)` (`lam_on_base_iff`), and `|Λ(2,0) Λ(2,f−2)| = (f−2)·f²`. -/
theorem L2_length {e f x : ℝ} (hf2 : 2 ≤ f) :
    dist (lam e f x 2 0) (lam e f x 2 (f - 2)) = (f - 2) * f ^ 2 := by
  have hsc3 := sin_sq_add_cos_sq (3 * x)
  have hnn : 0 ≤ (f - 2) * f ^ 2 := mul_nonneg (by linarith) (by positivity)
  have hsq : dist (lam e f x 2 0) (lam e f x 2 (f - 2)) ^ 2 = ((f - 2) * f ^ 2) ^ 2 := by
    unfold lam pP pJ; simp only [mkPt_zero, mkPt_one]; rw [dist_sq_mkPt]
    linear_combination ((f - 2) * f ^ 2) ^ 2 * hsc3
  exact (pow_left_inj₀ dist_nonneg hnn two_ne_zero).mp hsq

/-- `L₂`'s base point `Λ(2, f−2)` is on the base (`i + k = f`), and consecutive `L₂` points are `c`
apart (the second strip's row junctions `Q^L_k + P′ = Λ(2,k)`). -/
theorem L2_base_and_step {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (hcos : 0 < cos x) (k : ℝ) :
    (lam e f x 2 (f - 2)) 1 = (pJ f x f) 1 ∧
      dist (lam e f x 2 k) (lam e f x 2 (k + 1)) = f ^ 2 := by
  refine ⟨(lam_on_base_iff he hef hs hcos 2 (f - 2)).mpr (by ring), ?_⟩
  have hsc3 := sin_sq_add_cos_sq (3 * x)
  have hsq : dist (lam e f x 2 k) (lam e f x 2 (k + 1)) ^ 2 = (f ^ 2) ^ 2 := by
    unfold lam pP pJ; simp only [mkPt_zero, mkPt_one]; rw [dist_sq_mkPt]
    linear_combination (f ^ 2) ^ 2 * hsc3
  exact (pow_left_inj₀ dist_nonneg (sq_nonneg f) two_ne_zero).mp hsq

/-- **The row segments have length `2a`**: `|Λ(2,k) J_{k+2}| = 2·ef` (R6 step (b)). -/
theorem row_segment_two_a {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (k : ℝ) : dist (lam e f x 2 k) (pJ f x (k + 2)) = 2 * (e * f) := by
  have hf : 0 < f := he.trans hef
  rw [lam_eq_J_add hf.ne' hs, show (2 : ℝ) + k = k + 2 by ring]
  have hnn : 0 ≤ 2 * (e * f) := by positivity
  have hsq : dist (mkPt ((pJ f x (k + 2)) 0 + 2 * (e * f)) ((pJ f x (k + 2)) 1)) (pJ f x (k + 2)) ^ 2
      = (2 * (e * f)) ^ 2 := by
    unfold pJ; simp only [mkPt_zero, mkPt_one]; rw [dist_sq_mkPt]; ring
  exact (pow_left_inj₀ dist_nonneg hnn two_ne_zero).mp hsq

end Erdos634.Draft.MirrorLevel2

#print axioms Erdos634.Draft.MirrorLevel2.kc_sub_b_not_mem
#print axioms Erdos634.Draft.MirrorLevel2.kc_sub_b_not_InS
#print axioms Erdos634.Draft.MirrorLevel2.end_step
#print axioms Erdos634.Draft.MirrorLevel2.e_sq_not_InS
#print axioms Erdos634.Draft.MirrorLevel2.a_sub_b_not_mem
#print axioms Erdos634.Draft.MirrorLevel2.a_sub_b_not_InS
#print axioms Erdos634.Draft.MirrorLevel2.two_a_only
#print axioms Erdos634.Draft.MirrorLevel2.two_a_sub_c_not_mem'
#print axioms Erdos634.Draft.MirrorLevel2.two_a_sub_b_not_mem
#print axioms Erdos634.Draft.MirrorLevel2.r6_hyps_satisfiable
#print axioms Erdos634.Draft.MirrorLevel2.r6_fails_N44
#print axioms Erdos634.Draft.MirrorLevel2.kc_sub_b_sharp_at_f
#print axioms Erdos634.Draft.MirrorLevel2.lam_closed
#print axioms Erdos634.Draft.MirrorLevel2.lam_eq_J_add
#print axioms Erdos634.Draft.MirrorLevel2.lam_on_base_iff
#print axioms Erdos634.Draft.MirrorLevel2.L2_length
#print axioms Erdos634.Draft.MirrorLevel2.L2_base_and_step
#print axioms Erdos634.Draft.MirrorLevel2.row_segment_two_a
