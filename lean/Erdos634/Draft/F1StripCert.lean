/-
Draft/F1StripCert.lean -- the data-independent half of the F1 strip bases (Erdos #634).

`f1_main` takes a `CongruentDissection` of the triangle `T_3` (target carrier `triR .. 3`) whose first
`5 b (a+b)` tiles lie in `{p <= b}` and whose last `4 b (a+b)` tiles lie in `{p >= b}` -- the data a
certificate module (`F1Strip78Base`, `F1Strip87Base`) supplies -- and concludes that `T_m` is dissected into
`m^2 b (a+b)` tiles for every `m >= 2`, with the side lengths of the target and of the tile.

How the strip lemma gets its two hypotheses from this single `T_3` dissection (`F1StripExtract`):
  * the tiles in `{p <= b}` tile the strip `S_3 = T_3 ∩ {p <= b}`           (hypothesis `S_{k+1}`, `k = 2`);
  * the tiles in `{p >= b}` tile `T_3 ∩ {p >= b}`, a translate by `(b,0)` of `T_2`  (hypothesis `T_k`).

`pc_zpt` reads the `p`-coordinate of a certificate vertex `(x,0,0,y)` (the point `(x, y sqrt3)`) as `(x-y)/a`.

CREDIT: Yan Zhang (arXiv 2512.22696) for the family; Laczkovich for strip decompositions.
UNAUDITED beyond the internal build.  No sorry, no native_decide.
-/
import Erdos634.Draft.F1StripDissect
import Erdos634.Draft.F1StripExtract
import Erdos634.Z3Real

namespace Erdos634.Draft.F1StripCert

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.RegionTiling Erdos634.Draft.F1StripGeom
  Erdos634.Draft.F1StripLemma Erdos634.Draft.F1StripDissect Erdos634.Draft.F1StripExtract
  Erdos634.Z3Real

noncomputable section

/-- **The `p`-coordinate of a certificate vertex** `(x,0,0,y)`, i.e. the point `(x, y√3)`: `(x-y)/a`. -/
theorem pc_zpt (v : ZPt) (h1 : v.2.1 = 0) (h2 : v.2.2.1 = 0) (a : ℝ) :
    pc a (mkPt (toR (zx v)) (toR (zy v))) = ((v.1 : ℝ) - v.2.2.2) / a := by
  have h3 : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  simp only [pc_mkPt, toR, zx, zy, h1, h2, r3]
  simp only [Int.cast_zero, zero_mul, add_zero, zero_add]
  field_simp

theorem pc_zpt_le {v : ZPt} (h1 : v.2.1 = 0) (h2 : v.2.2.1 = 0) {a c : ℝ} (ha : 0 < a) {K : ℤ}
    (hK : v.1 - v.2.2.2 ≤ K) (hc : (K : ℝ) ≤ c * a) :
    pc a (mkPt (toR (zx v)) (toR (zy v))) ≤ c := by
  rw [pc_zpt v h1 h2 a, div_le_iff₀ ha]
  have : ((v.1 : ℝ) - v.2.2.2) ≤ K := by exact_mod_cast hK
  linarith

theorem pc_zpt_ge {v : ZPt} (h1 : v.2.1 = 0) (h2 : v.2.2.1 = 0) {a c : ℝ} (ha : 0 < a) {K : ℤ}
    (hK : K ≤ v.1 - v.2.2.2) (hc : c * a ≤ (K : ℝ)) :
    c ≤ pc a (mkPt (toR (zx v)) (toR (zy v))) := by
  rw [pc_zpt v h1 h2 a, le_div_iff₀ ha]
  have : (K : ℝ) ≤ ((v.1 : ℝ) - v.2.2.2) := by exact_mod_cast hK
  linarith

/-- a tile whose three vertices have `p ≤ c` has `p ≤ c` on its whole carrier -/
theorem pc_le_tile {t : Tri} (a b c : ℝ) (h : ∀ k, pc a (t.pts k) ≤ c) :
    ∀ x ∈ t.carrier, pc a x ≤ c := by
  intro x hx
  have := Erdos634.CertGeom.le_of_forall_pts_le (t := t) (ch a b 1 0) (c := c)
    (fun k => by rw [ch_apply]; have := h k; linarith) x hx
  rw [ch_apply] at this
  linarith

/-- a tile whose three vertices have `p ≥ c` has `p ≥ c` on its whole carrier -/
theorem pc_ge_tile {t : Tri} (a b c : ℝ) (h : ∀ k, c ≤ pc a (t.pts k)) :
    ∀ x ∈ t.carrier, c ≤ pc a x := by
  intro x hx
  have := Erdos634.CertGeom.le_of_forall_pts_le (t := t) (ch a b (-1) 0) (c := -c)
    (fun k => by rw [ch_apply]; have := h k; linarith) x hx
  rw [ch_apply] at this
  linarith

/-- two triangles with the same vertices are equal -/
theorem tri_ext {T U : Tri} (h : T.pts = U.pts) : T = U := by
  cases T; cases U; simp at h; subst h; rfl

/-- **The three sides of the model tile** `u A`, `u B`, `u C`. -/
theorem model_dists {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) {u : ℝ} (hu : 0 < u)
    (hC : C * C = A * A + A * B + B * B) :
    dist ((model hA hB hu).pts 0) ((model hA hB hu).pts 1) = u * A ∧
    dist ((model hA hB hu).pts 1) ((model hA hB hu).pts 2) = u * B ∧
    dist ((model hA hB hu).pts 2) ((model hA hB hu).pts 0) = u * C := by
  have hA' := real_pos hA
  have hB' := real_pos hB
  have hC' : (C : ℝ) * C = (A : ℝ) * A + (A : ℝ) * B + (B : ℝ) * B := by exact_mod_cast hC
  have hr3 := r3_sq'
  have hr3p := r3_pos
  refine ⟨?_, ?_, ?_⟩
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt 0 0) (mkPt (u * (A : ℝ)) 0) ^ 2 = _
    rw [dist_sq_mkPt]; ring
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt (u * (A : ℝ)) 0) (mkPt (u * (A : ℝ) + u * B / 2) (u * (B : ℝ) * r3 / 2)) ^ 2 = _
    rw [dist_sq_mkPt]
    linear_combination ((u * (B : ℝ)) / 2) ^ 2 * hr3
  · refine eq_of_sq dist_nonneg (by positivity) ?_
    show dist (mkPt (u * (A : ℝ) + u * B / 2) (u * (B : ℝ) * r3 / 2)) (mkPt 0 0) ^ 2 = _
    rw [dist_sq_mkPt]
    linear_combination ((u * (B : ℝ)) / 2) ^ 2 * hr3 - u ^ 2 * hC'

/-- a tile with the three side lengths `u A`, `u B`, `u C` (given as squares) is congruent to the model -/
theorem model_congruent_of_sq {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) {u : ℝ} (hu : 0 < u)
    (hC : C * C = A * A + A * B + B * B) {M : Tri}
    (h01 : dist (M.pts 0) (M.pts 1) ^ 2 = (u * (A : ℝ)) ^ 2)
    (h12 : dist (M.pts 1) (M.pts 2) ^ 2 = (u * (B : ℝ)) ^ 2)
    (h20 : dist (M.pts 2) (M.pts 0) ^ 2 = (u * (C : ℝ)) ^ 2) :
    M.Congruent (model hA hB hu) := by
  obtain ⟨d1, d2, d3⟩ := model_dists hA hB hu hC
  have hA' := real_pos hA
  have hB' := real_pos hB
  have hC0 : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  refine Erdos634.SssCongruent.congruent_of_dist_three ?_ ?_ ?_
  · rw [d1]; exact eq_of_sq dist_nonneg (by positivity) h01
  · rw [d2]; exact eq_of_sq dist_nonneg (by positivity) h12
  · rw [d3]; exact eq_of_sq dist_nonneg (by positivity) h20

/-- **From one dissection of `T_3` to all `T_m`, `m ≥ 2`.** -/
theorem f1_main {A B C : ℕ} (hA : 0 < A) (hB : 0 < B) {u : ℝ} (hu : 0 < u)
    (hC : C * C = A * A + A * B + B * B) {N n₁ n₂ : ℕ} (hN : n₁ + n₂ = N)
    (hn₁ : n₁ = 5 * (B * (A + B))) (hn₂ : n₂ = 4 * (B * (A + B)))
    (D : CongruentDissection N)
    (hT : D.target.carrier = triR (u * A) (u * B) (A : ℝ) (B : ℝ) 3)
    (hM : D.model.Congruent (model hA hB hu))
    (hl : ∀ i : Fin N, i.val < n₁ → ∀ x ∈ (D.tile i).carrier, pc (u * A) x ≤ B)
    (hr : ∀ i : Fin N, n₁ ≤ i.val → ∀ x ∈ (D.tile i).carrier, (B : ℝ) ≤ pc (u * A) x) :
    ∀ m : ℕ, 2 ≤ m → ∃ E : CongruentDissection (m * m * (B * (A + B))),
      dist (E.target.pts 0) (E.target.pts 1) = (m : ℝ) * u * A * B ∧
      dist (E.target.pts 1) (E.target.pts 2) = (m : ℝ) * u * B * C ∧
      dist (E.target.pts 2) (E.target.pts 0) = (m : ℝ) * u * B * ((A : ℝ) + B) ∧
      dist (E.model.pts 0) (E.model.pts 1) = u * A ∧
      dist (E.model.pts 1) (E.model.pts 2) = u * B ∧
      dist (E.model.pts 2) (E.model.pts 0) = u * C := by
  intro m hm
  have ha := scale_pos hA hu
  have hb := scale_pos hB hu
  have hA' := real_pos hA
  have hB' := real_pos hB
  set f := ch (u * (A : ℝ)) (u * (B : ℝ)) 1 0 with hf
  have hfx : ∀ x, f x = pc (u * (A : ℝ)) x := by
    intro x; rw [hf, ch_apply]; ring
  have hmem0 : (mkPt 0 0 : Plane) ∈ D.target.carrier := by
    rw [hT]
    simp only [triR, Set.mem_setOf_eq]
    rw [pc_c1_0 ha, qc_c1_0 hb]
    refine ⟨le_refl _, le_refl _, ?_⟩
    have : 0 < (3 : ℝ) * ((B : ℝ) * ((A : ℝ) + B)) := by positivity
    linarith
  have hmem1 : (mkPt (3 * (B : ℝ) * (u * (A : ℝ))) 0 : Plane) ∈ D.target.carrier := by
    rw [hT]
    simp only [triR, Set.mem_setOf_eq]
    rw [pc_t1 (B := (B : ℝ)) ha 3, qc_t1 (b := u * (B : ℝ)) (a := u * (A : ℝ)) (B := (B : ℝ)) 3]
    refine ⟨by positivity, le_refl _, ?_⟩
    linarith
  obtain ⟨hS, hTT⟩ := split_tiled_thr hN D f (B : ℝ)
    (fun i hi x hx => by rw [hfx]; exact hl i hi x hx)
    (fun i hi x hx => by rw [hfx]; exact hr i hi x hx)
    ⟨mkPt 0 0, hmem0, by rw [hfx, pc_c1_0 ha]; exact hB'⟩
    ⟨mkPt (3 * (B : ℝ) * (u * (A : ℝ))) 0, hmem1, by
      rw [hfx, pc_t1 (B := (B : ℝ)) ha 3]; linarith⟩
  -- the strip S_3
  have hS3 : Tiled (stripR (u * (A : ℝ)) (u * (B : ℝ)) (A : ℝ) (B : ℝ) (((2 + 1 : ℕ)) : ℝ))
      (model hA hB hu) ((2 * 2 + 1) * (B * (A + B))) := by
    have h1 := Tiled.remodel hS hM
    refine (h1.congr_count (by omega)).congr_set ?_
    ext x
    rw [hT]
    simp only [Set.mem_setOf_eq, triR, stripR, hfx]
    push_cast
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨h1, h4, h2, by linarith⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨⟨h1, h3, by linarith⟩, h2⟩
  -- T_2, as a translate of the tiles in {p >= b}
  have hT2 : Tiled (triR (u * (A : ℝ)) (u * (B : ℝ)) (A : ℝ) (B : ℝ) ((2 : ℕ) : ℝ))
      (model hA hB hu) (2 * 2 * (B * (A + B))) := by
    have h1 := (Tiled.remodel hTT hM).shift (-(psiPt (u * (A : ℝ)) (u * (B : ℝ)) (B : ℝ) 0))
    refine (h1.congr_count (by omega)).congr_set ?_
    ext x
    simp only [neg_neg, Set.mem_setOf_eq, hfx, pc_add, qc_add, pc_psi ha, qc_psi hb]
    rw [hT]
    simp only [Set.mem_setOf_eq, triR, pc_add, qc_add, pc_psi ha, qc_psi hb]
    push_cast
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      refine ⟨by linarith, by linarith, ?_⟩
      nlinarith
    · rintro ⟨h1, h2, h3⟩
      refine ⟨⟨by linarith, by linarith, ?_⟩, by linarith⟩
      nlinarith
  obtain ⟨i, rfl⟩ : ∃ i, m = 2 + i := ⟨m - 2, by omega⟩
  have key := strip_lemma hA hB hu 2 (by norm_num) hT2 hS3 i
  exact dissection_of_tiled hA hB hu hC (2 + i) (by omega) _ key

end

end Erdos634.Draft.F1StripCert

#print axioms Erdos634.Draft.F1StripCert.f1_main
