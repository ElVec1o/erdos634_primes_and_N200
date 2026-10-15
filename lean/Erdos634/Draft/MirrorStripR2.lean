-- Draft/MirrorStripR2.lean — formalization of R2: the mirror
-- branch (M) at the pierced corner is impossible at every m = 1 coprime member.
-- Imported directly by All.lean.  This file contains no `sorry`:
--   §1  Lemma A (arithmetic heart), as a corollary of `SideNoB.side_no_b_uncond`, plus the m ≥ 2
--       failure witnesses at (e,f) = (1,2) (so the m = 1 hypothesis is necessary);
--   §2  the metric pieces of R2's strip, over the reals, in the conventions of ThickEFminus1Probe
--       (sin(α/2) = e/(2f), x = α/2, apex at the origin, axis downward).
import Erdos634.SideNoB
import Erdos634.CertCoord
import Erdos634.Inflation

namespace Erdos634.Draft.MirrorStripR2

/-! ## §1 Lemma A

Lemma A is `Inflation.c_side_no_b` ("the `c`-side of a scale-`k` inflation, `k < f`, carries no
`b`-edge"), proved by a mod-`f` / mod-`e` descent.  The statement of R2's Lemma A is that theorem verbatim.
`lemmaA_nb_zero` below is a second, two-line proof via `side_no_b_uncond` (the padding argument),
without the `1 ≤ e` hypothesis; `lemmaA_via_corpus` checks that the statements agree. -/

/-- **Lemma A (R2).** At `m = 1`, for `k < f` (i.e. `k ≤ f − 1`), every representation
`k·c = n_a·a + n_b·b + n_c·c` with `(a,b,c) = (ef, b, f²)`, `b + e² = f²`, has `n_b = 0`.
Hypotheses are exactly those of `SideNoB.side_no_b_uncond` (coprime, `e < f`) plus `k < f`;
`1 ≤ e` and `1 ≤ k` are not needed.  Proof: pad with `f − k` copies of `c` to get a side walk
`f³ = n_a a + n_b b + (n_c + f − k) c` with `R' = n_c + f − k ≥ 1`. -/
theorem lemmaA_nb_zero {e f b k na nb nc : ℕ} (hco : Nat.Coprime e f) (hef : e < f)
    (hb : b + e * e = f * f) (hk : k < f)
    (h : na * (e * f) + nb * b + nc * (f * f) = k * (f * f)) : nb = 0 := by
  have h1 : (nc + (f - k)) * (f * f) = nc * (f * f) + (f - k) * (f * f) := by ring
  have h2 : k * (f * f) + (f - k) * (f * f) = f * f * f := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' hk.le]; ring
  have hwalk : na * (e * f) + nb * b + (nc + (f - k)) * (f * f) = f * f * f := by
    rw [h1]; omega
  exact SideNoB.side_no_b_uncond hco hef hb hwalk (by omega)

/-- **Lemma A, paper form**: `(a,b,c) = (ef, f²−e², f²)`, `1 ≤ k ≤ f − 1`. -/
theorem lemmaA (e f k na nb nc : ℕ) (hco : Nat.Coprime e f) (hef : e < f)
    (hkf : k ≤ f - 1)
    (h : na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = k * f ^ 2) : nb = 0 := by
  have hee : e * e ≤ f * f := Nat.mul_le_mul hef.le hef.le
  have hb : (f ^ 2 - e ^ 2) + e * e = f * f := by
    rw [sq, sq]; omega
  have hk : k < f := by omega
  have h' : na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * (f * f) = k * (f * f) := by
    rw [← sq]; exact h
  exact lemmaA_nb_zero hco hef hb hk h'

/-- The corpus form: R2's Lemma A is `Inflation.c_side_no_b`. -/
theorem lemmaA_via_corpus (e f k na nb nc : ℕ) (he : 1 ≤ e) (hco : Nat.Coprime e f) (hef : e < f)
    (hkf : k ≤ f - 1)
    (h : na * (e * f) + nb * (f ^ 2 - e ^ 2) + nc * f ^ 2 = k * f ^ 2) : nb = 0 := by
  have hee : e ^ 2 ≤ f ^ 2 := Nat.pow_le_pow_left hef.le 2
  exact Inflation.c_side_no_b e f (f ^ 2 - e ^ 2) k na nb nc he hef hco (by omega) (by omega) h

/-- Non-vacuity of Lemma A's hypotheses: at `(e,f,k) = (2,5,3)`, `3·25 = 5·10 + 1·25`. -/
theorem lemmaA_hyps_satisfiable :
    Nat.Coprime 2 5 ∧ 2 < 5 ∧ 3 ≤ 5 - 1 ∧
      5 * (2 * 5) + 0 * (5 ^ 2 - 2 ^ 2) + 1 * 5 ^ 2 = 3 * 5 ^ 2 := by decide

/-- **The m = 1 hypothesis is necessary (N = 44, m = 2).** At `(e,f) = (1,2)`, `(a,b,c) = (2,3,4)`,
the line `L` has length `(2f−1)c = 12 = 4·b`: Lemma A's conclusion fails at `k = 2f − 1 = 3`. -/
theorem lemmaA_fails_m2 :
    0 * (1 * 2) + 4 * (2 ^ 2 - 1 ^ 2) + 0 * 2 ^ 2 = 3 * 2 ^ 2 ∧
    ¬ ∀ na nb nc : ℕ, na * (1 * 2) + nb * (2 ^ 2 - 1 ^ 2) + nc * 2 ^ 2 = 3 * 2 ^ 2 → nb = 0 := by
  refine ⟨by decide, fun hall => ?_⟩
  have := hall 0 4 0 (by decide)
  omega

/-- The same at `m = 3` (N = 99): `(3f−1)c = 20 = 7a + 2b` at `(1,2)`. -/
theorem lemmaA_fails_m3 :
    ¬ ∀ na nb nc : ℕ, na * (1 * 2) + nb * (2 ^ 2 - 1 ^ 2) + nc * 2 ^ 2 = 5 * 2 ^ 2 → nb = 0 := by
  intro hall
  have := hall 7 2 0 (by decide)
  omega

/-- And the underlying side-walk fact fails at `m = 2`: the side `2f³ = 16` at `(1,2)` is
`4·b + 1·c` with a `c` present. -/
theorem side_walk_has_b_m2 : 0 * (1 * 2) + 4 * (2 ^ 2 - 1 ^ 2) + 1 * 2 ^ 2 = 2 * 2 ^ 3 := by
  decide

/-! ## §2 The metric pieces of the strip

Coordinates: apex `A` at the origin, axis pointing down; `x = α/2` with `sin x = e/(2f)`.  The
direction at angle `θ` from the axis (positive to the right) is `(sin θ, −cos θ)`.  `(a,b,c) =
(ef, f²−e², f²)` as reals.  T₂ = `(A, V, P′)` with `V` at distance `c` on the right inner ray and
`P′` at distance `b` on the left inner ray (so T₂ has α at A, β at V, γ at P′, VP′ = a).  The left leg
has unit direction `u_L = (−sin 3x, −cos 3x)`; `J_j = j·c·u_L`; `Q_j = P′ + j·c·u_L` (the points of
the line `L` through `P′` parallel to the leg); `A* = P′ + b·u_L`. -/

open Real Erdos634.Geometry Erdos634.CertCoord

theorem plane_ext' {u w : Plane} (h0 : u 0 = w 0) (h1 : u 1 = w 1) : u = w := by
  ext i; fin_cases i <;> simpa

theorem lineMap_mkPt' (a b c d t : ℝ) :
    AffineMap.lineMap (mkPt a b) (mkPt c d) t = mkPt (a + t * (c - a)) (b + t * (d - b)) := by
  apply plane_ext' <;> simp [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add] <;> ring

/-- `P′`: distance `b` from the apex on the left inner ray. -/
noncomputable def pP (e f x : ℝ) : Plane :=
  mkPt (-(f ^ 2 - e ^ 2) * sin x) (-(f ^ 2 - e ^ 2) * cos x)
/-- `V`: distance `c` from the apex on the right inner ray. -/
noncomputable def pV (f x : ℝ) : Plane := mkPt (f ^ 2 * sin x) (-(f ^ 2) * cos x)
/-- `J_j = j·c·u_L`, the leg point at distance `j·c` from the apex (`J_f` the base corner). -/
noncomputable def pJ (f x j : ℝ) : Plane :=
  mkPt (-(j * f ^ 2) * sin (3 * x)) (-(j * f ^ 2) * cos (3 * x))
/-- `Q_j = P′ + j·c·u_L`, the point of `L` at distance `j·c` from `P′`. -/
noncomputable def pQ (e f x j : ℝ) : Plane :=
  mkPt (-(f ^ 2 - e ^ 2) * sin x - j * f ^ 2 * sin (3 * x))
    (-(f ^ 2 - e ^ 2) * cos x - j * f ^ 2 * cos (3 * x))
/-- `A* = P′ + b·u_L`. -/
noncomputable def pAstar (e f x : ℝ) : Plane :=
  mkPt (-(f ^ 2 - e ^ 2) * sin x - (f ^ 2 - e ^ 2) * sin (3 * x))
    (-(f ^ 2 - e ^ 2) * cos x - (f ^ 2 - e ^ 2) * cos (3 * x))
/-- The right base corner `f³·(sin 3x, −cos 3x)`. -/
noncomputable def pRight (f x : ℝ) : Plane := mkPt (f ^ 3 * sin (3 * x)) (-(f ^ 3) * cos (3 * x))

/-- **lem:apexid in the strip's form.** `c·sin 3x − b·sin x = a` and `c·cos 3x = b·cos x`:
the vector `P′ − c·u_L` is exactly `(a, 0)`. -/
theorem apex_offsets {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) :
    f ^ 2 * sin (3 * x) - (f ^ 2 - e ^ 2) * sin x = e * f ∧
      f ^ 2 * cos (3 * x) = (f ^ 2 - e ^ 2) * cos x := by
  have he : e = 2 * f * sin x := by rw [hs]; field_simp
  have hsc := sin_sq_add_cos_sq x
  rw [sin_three_mul, cos_three_mul]
  subst he
  constructor
  · ring
  · linear_combination (4 * f ^ 2 * cos x) * hsc

theorem pQ_zero (e f x : ℝ) : pQ e f x 0 = pP e f x := by
  unfold pQ pP; congr 1 <;> ring

/-- `A*` is the point of `L` at distance `b` from `P′` (parameter `b/c` in units of `c`). -/
theorem pAstar_eq_pQ {e f x : ℝ} (hf : f ≠ 0) :
    pAstar e f x = pQ e f x ((f ^ 2 - e ^ 2) / f ^ 2) := by
  unfold pAstar pQ; rw [div_mul_cancel₀ _ (pow_ne_zero 2 hf)]

/-- `Q_j = J_{j+1} + (a, 0)`: every strip junction on `L` sits horizontally `a` right of the leg. -/
theorem pQ_eq_pJ_add {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) (j : ℝ) :
    pQ e f x j = mkPt ((pJ f x (j + 1)) 0 + e * f) ((pJ f x (j + 1)) 1) := by
  obtain ⟨h1, h2⟩ := apex_offsets hf hs
  unfold pQ pJ; simp only [mkPt_zero, mkPt_one]
  congr 1
  · linear_combination h1
  · linear_combination h2

private theorem dist_eq_of_sq {p q : Plane} {L : ℝ} (hL : 0 ≤ L) (h : dist p q ^ 2 = L ^ 2) :
    dist p q = L := by
  have := dist_nonneg (x := p) (y := q)
  nlinarith [sq_nonneg (dist p q - L), sq_nonneg (dist p q + L)]

/-- **The strip cells have the tile's side lengths.**  With `Z_j = (Q_j, J_{j+1}, Q_{j+1})` and
`Z′_j = (J_{j+1}, J_{j+2}, Q_{j+1})`: `|Q_j J_{j+1}| = a`, `|Q_{j+1} J_{j+1}| = b`, `|Q_j Q_{j+1}| = c`,
`|J_{j+1} J_{j+2}| = c`, `|Q_{j+1} J_{j+2}| = a`. -/
theorem strip_cell_sides {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (j : ℝ) :
    dist (pQ e f x j) (pJ f x (j + 1)) = e * f ∧
    dist (pQ e f x (j + 1)) (pJ f x (j + 1)) = f ^ 2 - e ^ 2 ∧
    dist (pQ e f x j) (pQ e f x (j + 1)) = f ^ 2 ∧
    dist (pJ f x (j + 1)) (pJ f x (j + 2)) = f ^ 2 ∧
    dist (pQ e f x (j + 1)) (pJ f x (j + 2)) = e * f := by
  have hf : 0 < f := he.trans hef
  obtain ⟨h1, h2⟩ := apex_offsets hf.ne' hs
  have hsc := sin_sq_add_cos_sq x
  have hsc3 := sin_sq_add_cos_sq (3 * x)
  have hb : 0 ≤ f ^ 2 - e ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he hf)]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply dist_eq_of_sq (by positivity)
    unfold pQ pJ; rw [dist_sq_mkPt]
    linear_combination (f ^ 2 * sin (3 * x) - (f ^ 2 - e ^ 2) * sin x + e * f) * h1
      + (f ^ 2 * cos (3 * x) - (f ^ 2 - e ^ 2) * cos x) * h2
  · apply dist_eq_of_sq hb
    unfold pQ pJ; rw [dist_sq_mkPt]
    linear_combination (f ^ 2 - e ^ 2) ^ 2 * hsc
  · apply dist_eq_of_sq (by positivity)
    unfold pQ; rw [dist_sq_mkPt]
    linear_combination (f ^ 2) ^ 2 * hsc3
  · apply dist_eq_of_sq (by positivity)
    unfold pJ; rw [dist_sq_mkPt]
    linear_combination (f ^ 2) ^ 2 * hsc3
  · apply dist_eq_of_sq (by positivity)
    unfold pQ pJ; rw [dist_sq_mkPt]
    linear_combination (f ^ 2 * sin (3 * x) - (f ^ 2 - e ^ 2) * sin x + e * f) * h1
      + (f ^ 2 * cos (3 * x) - (f ^ 2 - e ^ 2) * cos x) * h2

/-- `cos 3x > 0` (from `c·cos 3x = b·cos x`) and `sin 3x > 0` (from `c·sin 3x = a + b·sin x`). -/
theorem trig3_pos {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (hcos : 0 < cos x) : 0 < cos (3 * x) ∧ 0 < sin (3 * x) := by
  have hf : 0 < f := he.trans hef
  obtain ⟨h1, h2⟩ := apex_offsets hf.ne' hs
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he hf)]
  have hsin : 0 < sin x := by rw [hs]; positivity
  have hf2 : 0 < f ^ 2 := by positivity
  constructor
  · have : 0 < f ^ 2 * cos (3 * x) := by rw [h2]; exact mul_pos hb hcos
    exact pos_of_mul_pos_right this hf2.le
  · have : 0 < f ^ 2 * sin (3 * x) := by
      have h3 : f ^ 2 * sin (3 * x) = e * f + (f ^ 2 - e ^ 2) * sin x := by linear_combination h1
      rw [h3]; have := mul_pos he hf; have := mul_pos hb hsin; linarith
    exact pos_of_mul_pos_right this hf2.le

/-- **(M) mirror placement.**  Every point of the line `VP′` is equidistant from `A` and from
`A* = P′ + b·u_L`.  With `A* ≠ A` (`pAstar_ne_apex`) this says the line `VP′` is the perpendicular
bisector of `AA*`: `A*` is the mirror of the apex across `VP′`, i.e. the mirror `M` of `T₂` across
`VP′` has its `b`-edge `P′A*` along `L`, starting at `P′`, in the direction `u_L`. -/
theorem pAstar_mirror {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) (t : ℝ) :
    dist (pAstar e f x) (AffineMap.lineMap (pP e f x) (pV f x) t)
      = dist (mkPt 0 0) (AffineMap.lineMap (pP e f x) (pV f x) t) := by
  have he : e = 2 * f * sin x := by rw [hs]; field_simp
  have hsc := sin_sq_add_cos_sq x
  have hsq : dist (pAstar e f x) (AffineMap.lineMap (pP e f x) (pV f x) t) ^ 2
      = dist (mkPt 0 0) (AffineMap.lineMap (pP e f x) (pV f x) t) ^ 2 := by
    unfold pAstar pP pV
    rw [lineMap_mkPt', dist_sq_mkPt, dist_sq_mkPt, sin_three_mul, cos_three_mul]
    subst he
    linear_combination (8 * f ^ 4 * (2 * sin x - 1) * (2 * sin x + 1) *
      (8 * cos x ^ 4 * sin x ^ 2 - 2 * cos x ^ 4 - 8 * cos x ^ 2 * sin x ^ 4
        + 4 * cos x ^ 2 * sin x ^ 2 * t - 2 * cos x ^ 2 * sin x ^ 2 + cos x ^ 2
        + 8 * sin x ^ 6 - 4 * sin x ^ 4 * t - 6 * sin x ^ 4 + 2 * sin x ^ 2 * t
        + sin x ^ 2)) * hsc
  exact (pow_left_inj₀ dist_nonneg dist_nonneg two_ne_zero).mp hsq

theorem pAstar_ne_apex {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (hcos : 0 < cos x) : pAstar e f x ≠ mkPt 0 0 := by
  intro h
  have hy := congrArg (fun p : Plane => p 1) h
  simp only [pAstar, mkPt_one] at hy
  have hb : 0 < f ^ 2 - e ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he (he.trans hef))]
  obtain ⟨hc3, -⟩ := trig3_pos he hef hs hcos
  nlinarith [mul_pos hb hcos, mul_pos hb hc3]

/-- **The line `L` meets the base exactly at `Q_{f−1}`**: the point `Q_j = P′ + j·c·u_L` is at the
base's depth (that of the base corner `J_f`) iff `j = f − 1`.  So `L` runs from `P′` to the base
with length exactly `(f−1)·c` (`dist_P_Qbase`). -/
theorem pQ_on_base_iff {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (hcos : 0 < cos x) (j : ℝ) :
    (pQ e f x j) 1 = (pJ f x f) 1 ↔ j = f - 1 := by
  have hf : 0 < f := he.trans hef
  obtain ⟨-, h2⟩ := apex_offsets hf.ne' hs
  obtain ⟨hc3, -⟩ := trig3_pos he hef hs hcos
  simp only [pQ, pJ, mkPt_one]
  constructor
  · intro h
    have h' : (j + 1 - f) * (f ^ 2 * cos (3 * x)) = 0 := by linear_combination -h + h2
    rcases mul_eq_zero.mp h' with h0 | h0
    · linarith
    · exfalso; have := mul_pos (pow_pos hf 2) hc3; linarith
  · rintro rfl; linear_combination h2

/-- `|P′ Q_{f−1}| = (f−1)·c`. -/
theorem dist_P_Qbase {e f x : ℝ} (hf1 : 1 ≤ f) :
    dist (pP e f x) (pQ e f x (f - 1)) = (f - 1) * f ^ 2 := by
  have hsc3 := sin_sq_add_cos_sq (3 * x)
  have hnn : 0 ≤ (f - 1) * f ^ 2 := mul_nonneg (by linarith) (by positivity)
  apply dist_eq_of_sq hnn
  unfold pP pQ; rw [dist_sq_mkPt]
  linear_combination ((f - 1) * f ^ 2) ^ 2 * hsc3

/-- **`Q_{f−1}` is a point of the base, strictly between its corners**: it is `J_f + (a, 0)`, and
`J_f.x < Q_{f−1}.x < (right corner).x` (the last is `a < e(3f² − e²)`, needing `f ≥ 1`). -/
theorem Qbase_on_base {e f x : ℝ} (he : 0 < e) (hef : e < f) (hf1 : 1 ≤ f)
    (hs : sin x = e / (2 * f)) :
    pQ e f x (f - 1) = mkPt ((pJ f x f) 0 + e * f) ((pJ f x f) 1) ∧
      (pJ f x f) 0 < (pQ e f x (f - 1)) 0 ∧ (pQ e f x (f - 1)) 0 < (pRight f x) 0 ∧
      (pRight f x) 1 = (pJ f x f) 1 := by
  have hf : 0 < f := he.trans hef
  have hQ := pQ_eq_pJ_add hf.ne' hs (f - 1)
  rw [sub_add_cancel] at hQ
  obtain ⟨h1, -⟩ := apex_offsets hf.ne' hs
  have hsin : 0 < sin x := by rw [hs]; positivity
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he hf)]
  refine ⟨hQ, ?_, ?_, ?_⟩
  · rw [hQ]; simp only [mkPt_zero]; have := mul_pos he hf; linarith
  · rw [hQ]; simp only [pJ, pRight, mkPt_zero]
    -- f³·sin 3x = f·(ef + b·sin x); need  ef < 2·f·(ef + b·sin x)
    have hk : f ^ 3 * sin (3 * x) = f * (e * f + (f ^ 2 - e ^ 2) * sin x) := by
      linear_combination f * h1
    have hpos : 0 < (f ^ 2 - e ^ 2) * sin x := mul_pos hb hsin
    have hef1 : e * f ≤ f * (e * f) := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hf1) (mul_pos he hf).le]
    nlinarith [mul_pos hf hpos, mul_pos he hf, hk, hef1]
  · simp only [pJ, pRight, mkPt_one]; ring

/-- **The two sides of `L`.**  With `g X = cos 3x·(X₀ − P′₀) − sin 3x·(X₁ − P′₁)` (a normal
functional to `L`, zero on `L`): `g = 0` on every `Q_j` (in particular on `P′` and `A*`),
`g(V) > 0`, and `g(J_j) = −a·cos 3x < 0` on every leg point.  So `M = (V, P′, A*)` lies on the
closed side `{g ≥ 0}` (the band side) and the leg — hence every strip cell `Z_j`, `Z′_j` — on
`{g ≤ 0}` (the strip side). -/
theorem sides_of_L {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f))
    (hcos : 0 < cos x) :
    let g : Plane → ℝ := fun X =>
      cos (3 * x) * (X 0 - (pP e f x) 0) - sin (3 * x) * (X 1 - (pP e f x) 1)
    (∀ j, g (pQ e f x j) = 0) ∧ g (pAstar e f x) = 0 ∧ 0 < g (pV f x) ∧
      ∀ j, g (pJ f x j) = -(e * f) * cos (3 * x) ∧ g (pJ f x j) < 0 := by
  intro g
  have hf : 0 < f := he.trans hef
  obtain ⟨h1, h2⟩ := apex_offsets hf.ne' hs
  obtain ⟨hc3, hs3⟩ := trig3_pos he hef hs hcos
  have hsin : 0 < sin x := by rw [hs]; positivity
  refine ⟨fun j => ?_, ?_, ?_, fun j => ?_⟩
  · simp only [g, pQ, pP, mkPt_zero, mkPt_one]; ring
  · simp only [g, pAstar, pP, mkPt_zero, mkPt_one]; ring
  · simp only [g, pV, pP, mkPt_zero, mkPt_one]
    have hd : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he hf)]
    have k1 := mul_pos (mul_pos hsin hc3) hd
    have k2 := mul_pos (mul_pos hcos hs3) (pow_pos he 2)
    nlinarith [k1, k2]
  · have hval : g (pJ f x j) = -(e * f) * cos (3 * x) := by
      simp only [g, pJ, pP, mkPt_zero, mkPt_one]
      linear_combination (-cos (3 * x)) * h1 + sin (3 * x) * h2
    refine ⟨hval, ?_⟩
    rw [hval]; have := mul_pos (mul_pos he hf) hc3; linarith

/-- **T₂'s sides** in the frame: `|A P′| = b`, `|A V| = c`, `|V P′| = a` (so T₂ = (A, V, P′) is the
tile, with `α` at `A`). -/
theorem apex_tile_sides {e f x : ℝ} (he : 0 < e) (hef : e < f) (hs : sin x = e / (2 * f)) :
    dist (mkPt 0 0) (pP e f x) = f ^ 2 - e ^ 2 ∧ dist (mkPt 0 0) (pV f x) = f ^ 2 ∧
      dist (pV f x) (pP e f x) = e * f := by
  have hf : 0 < f := he.trans hef
  have hsc := sin_sq_add_cos_sq x
  have hb : 0 ≤ f ^ 2 - e ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he hf)]
  refine ⟨?_, ?_, ?_⟩
  · apply dist_eq_of_sq hb
    unfold pP; rw [dist_sq_mkPt]
    linear_combination (f ^ 2 - e ^ 2) ^ 2 * hsc
  · apply dist_eq_of_sq (by positivity)
    unfold pV; rw [dist_sq_mkPt]
    linear_combination (f ^ 2) ^ 2 * hsc
  · apply dist_eq_of_sq (by positivity)
    have he2 : e = 2 * f * sin x := by rw [hs]; field_simp
    unfold pV pP; rw [dist_sq_mkPt]
    subst he2
    linear_combination (16 * f ^ 4 * sin x ^ 4) * hsc

end Erdos634.Draft.MirrorStripR2

#print axioms Erdos634.Draft.MirrorStripR2.lemmaA_nb_zero
#print axioms Erdos634.Draft.MirrorStripR2.lemmaA
#print axioms Erdos634.Draft.MirrorStripR2.lemmaA_via_corpus
#print axioms Erdos634.Draft.MirrorStripR2.lemmaA_hyps_satisfiable
#print axioms Erdos634.Draft.MirrorStripR2.lemmaA_fails_m2
#print axioms Erdos634.Draft.MirrorStripR2.lemmaA_fails_m3
#print axioms Erdos634.Draft.MirrorStripR2.side_walk_has_b_m2
#print axioms Erdos634.Draft.MirrorStripR2.apex_offsets
#print axioms Erdos634.Draft.MirrorStripR2.pQ_zero
#print axioms Erdos634.Draft.MirrorStripR2.pAstar_eq_pQ
#print axioms Erdos634.Draft.MirrorStripR2.pQ_eq_pJ_add
#print axioms Erdos634.Draft.MirrorStripR2.strip_cell_sides
#print axioms Erdos634.Draft.MirrorStripR2.trig3_pos
#print axioms Erdos634.Draft.MirrorStripR2.pAstar_mirror
#print axioms Erdos634.Draft.MirrorStripR2.pAstar_ne_apex
#print axioms Erdos634.Draft.MirrorStripR2.pQ_on_base_iff
#print axioms Erdos634.Draft.MirrorStripR2.dist_P_Qbase
#print axioms Erdos634.Draft.MirrorStripR2.Qbase_on_base
#print axioms Erdos634.Draft.MirrorStripR2.sides_of_L
#print axioms Erdos634.Draft.MirrorStripR2.apex_tile_sides
