-- Draft/ThetaComposeGlue.lean -- the GLUING STEP behind the tile count 778855 = theta_119(3,8) = W_55 u alpha_8.  UNAUDITED.
-- No sorry, no native_decide.
/-
**Gluing a `W` piece and an `alpha` piece along a cevian into the isosceles triangle `theta`.**

Geometry (Work item C identity, `internal working notes` section 2; construction
`internal working notes`).  Tile `(e f, b, f^2)`, `b = f^2 - e^2`, `Q = 2 f^2 - e^2`, any real `M > 0`.

* `alpha` piece: isosceles, base `M f Q`, legs `M f^3` (this is `alpha_g` with `g b = M f`).
* `W` piece: sides `(M f b, M e Q, M f^3)` (this is `W_M(e,f)`).
* Put the `alpha` piece with apex `O` and base `P B`.  Extend the leg `P O` beyond `O` to `C` with
  `|P C| = (Q / f^2) |P O| = M f Q`.  Then `|O C| = M f b`, `|C B| = M e Q` (law of cosines in the
  `alpha` triangle), so the triangle `B O C` has the sides of `W_M`, and `B P C` is isosceles with
  legs `M f Q` and base `M e Q`.  The cevian is `B O`; `P, O, C` are collinear by construction.
* THE GENERAL GLUING LEMMA ALREADY EXISTS in the corpus and is used here, not re-proved:
  `UnionDissection.unionCongruentDissection` (union of two dissections of the same model whose
  targets have disjoint interiors and union to the target), the cevian lemmas
  `CVCCevianCut.fan_cover` / `fan_disjoint`, and the transport `CVCCevianCut.transport`
  (move a dissection onto any congruent triangle, by an isometry; `Ladder.isoAff`).

Result: `glue_cevian`.  Given a `CongruentDissection` whose target has the sides of `W_M` and one whose
target has the sides of `alpha` (both with model of sides `(e f, b, f^2)`), the union is a
`CongruentDissection` with `N1 + N2` tiles whose target has the sides of `theta` (legs `M f Q`,
base `M e Q`).  The placement of the two pieces is exact (explicit vectors), not asserted.

CREDIT: identity `theta_{jQ}(e,f) = W_{jb}(e,f) u alpha_{jf}(e,f)`: Work item C (NEWWAYS_C, 2026-10-20);
the `theta` family and its up-set: D. Paliy; `W`, `T`, base-beta framework: M. Beeson and I. Rosu; the
cevian cut pattern is the project's own `CVCCevianCut` (Herdt-style fan cut).
-/
import Erdos634.Draft.CVCCevianCut

namespace Erdos634.Draft.ThetaComposeGlue

open Erdos634.Geometry Erdos634.Draft.CVCCevianCut
open Erdos634.Draft.FDBBaseBetaE1 (HasSides congruent_of_hasSides)

/-- SSS in the two-sided form: two triangles having the same side data are congruent. -/
theorem congruent_of_hasSides_both {T U : Tri} {a b c : ℝ} (hT : HasSides T a b c)
    (hU : HasSides U a b c) : T.Congruent U := by
  obtain ⟨τ, h1, h2, h3⟩ := hU
  exact (congruent_of_hasSides hT (U := U.relabel τ) h1 h2 h3).trans (U.congruent_relabel τ).symm

/-- The same dissection with its model replaced by a congruent triangle. -/
noncomputable def remodel {N : ℕ} (D : CongruentDissection N) (M' : Tri) (h : D.model.Congruent M') :
    CongruentDissection N :=
  { D with
    model := M'
    tiles_congruent := fun i => (D.tiles_congruent i).trans h }

theorem set_perm_hull (a b c : Plane) : ({a, b, c} : Set Plane) = {c, b, a} := by
  ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; tauto

/-- **The gluing step.**  `W_M(e,f)` and `alpha` (base `M f Q`, legs `M f^3`) glued along the cevian
`B O` form the isosceles `theta` (legs `M f Q`, base `M e Q`). -/
theorem glue_cevian (e f M : ℝ) (he : 0 < e) (hef : e < f) (hM : 0 < M)
    {N1 N2 : ℕ} (D1 : CongruentDissection N1) (D2 : CongruentDissection N2)
    (h1t : HasSides D1.target (M * (f * (f ^ 2 - e ^ 2))) (M * (e * (2 * f ^ 2 - e ^ 2))) (M * f ^ 3))
    (h1m : HasSides D1.model (e * f) (f ^ 2 - e ^ 2) (f ^ 2))
    (h2t : HasSides D2.target (M * (f * (2 * f ^ 2 - e ^ 2))) (M * f ^ 3) (M * f ^ 3))
    (h2m : HasSides D2.model (e * f) (f ^ 2 - e ^ 2) (f ^ 2)) :
    ∃ D : CongruentDissection (N1 + N2),
      HasSides D.target (M * (f * (2 * f ^ 2 - e ^ 2))) (M * (f * (2 * f ^ 2 - e ^ 2)))
        (M * (e * (2 * f ^ 2 - e ^ 2))) ∧
      HasSides D.model (e * f) (f ^ 2 - e ^ 2) (f ^ 2) := by
  have hf : 0 < f := by linarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hQ : 0 < 2 * f ^ 2 - e ^ 2 := by nlinarith
  obtain ⟨τ, h12, h20, h01⟩ := h2t
  have hnd : cr (D2.target.pts (τ 0)) (D2.target.pts (τ 1)) (D2.target.pts (τ 2)) ≠ 0 :=
    cr_pts_ne_zero (D2.target.relabel τ)
  obtain ⟨O, hO⟩ : ∃ O, O = D2.target.pts (τ 0) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = D2.target.pts (τ 1) := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = D2.target.pts (τ 2) := ⟨_, rfl⟩
  rw [← hO, ← hP, ← hB] at hnd
  rw [← hP, ← hB] at h12
  rw [← hB, ← hO] at h20
  rw [← hO, ← hP] at h01
  have hPB := sqd_of_dist _ _ _ h12
  have hBO := sqd_of_dist _ _ _ h20
  have hOP := sqd_of_dist _ _ _ h01
  -- the point C and the parameter t
  obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = (2 * f ^ 2 - e ^ 2) / f ^ 2 := ⟨_, rfl⟩
  have hlam1 : lam - 1 = (f ^ 2 - e ^ 2) / f ^ 2 := by rw [hlam]; field_simp; ring
  have hlam1pos : 0 < lam - 1 := by rw [hlam1]; positivity
  obtain ⟨C, hC⟩ : ∃ C : Plane, C = P + lam • (O - P) := ⟨_, rfl⟩
  have hC0 : C 0 = P 0 + lam * (O 0 - P 0) := by rw [hC]; simp
  have hC1 : C 1 = P 1 + lam * (O 1 - P 1) := by rw [hC]; simp
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = f ^ 2 / (2 * f ^ 2 - e ^ 2) := ⟨_, rfl⟩
  have hQne : 2 * f ^ 2 - e ^ 2 ≠ 0 := hQ.ne'
  have htl : t * lam = 1 := by rw [ht, hlam]; field_simp; exact div_self (by intro h; linarith)
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : t < 1 := by rw [ht, div_lt_one hQ]; nlinarith
  have hOt : O = P + t • (C - P) := by
    have : C - P = lam • (O - P) := by rw [hC]; abel
    rw [this, smul_smul, htl, one_smul]; abel
  -- nondegeneracy
  have hcrBPC : cr B P C ≠ 0 := by
    have : cr B P C = -lam * cr O P B := by unfold cr; rw [hC0, hC1]; ring
    rw [this]; exact mul_ne_zero (by nlinarith) hnd
  have hcrBOC : cr B O C ≠ 0 := by
    have : cr B O C = (1 - lam) * cr O P B := by unfold cr; rw [hC0, hC1]; ring
    rw [this]; exact mul_ne_zero (by nlinarith) hnd
  -- distances
  have dOC : dist O C = M * (f * (f ^ 2 - e ^ 2)) := by
    refine dist_of_sqd _ _ _ (by positivity) ?_
    have key : (O 0 - C 0) ^ 2 + (O 1 - C 1) ^ 2 = (1 - lam) ^ 2 * ((O 0 - P 0) ^ 2 + (O 1 - P 1) ^ 2) := by
      rw [hC0, hC1]; ring
    rw [key, hOP, hlam]; field_simp; try ring
  have dCB : dist C B = M * (e * (2 * f ^ 2 - e ^ 2)) := by
    refine dist_of_sqd _ _ _ (by positivity) ?_
    have key : (C 0 - B 0) ^ 2 + (C 1 - B 1) ^ 2 =
        (1 - lam) * ((P 0 - B 0) ^ 2 + (P 1 - B 1) ^ 2) + lam * ((B 0 - O 0) ^ 2 + (B 1 - O 1) ^ 2)
          + (lam ^ 2 - lam) * ((O 0 - P 0) ^ 2 + (O 1 - P 1) ^ 2) := by
      rw [hC0, hC1]; ring
    rw [key, hPB, hBO, hOP, hlam]; field_simp; try ring
  have dPC : dist P C = M * (f * (2 * f ^ 2 - e ^ 2)) := by
    refine dist_of_sqd _ _ _ (by positivity) ?_
    have key : (P 0 - C 0) ^ 2 + (P 1 - C 1) ^ 2 = lam ^ 2 * ((O 0 - P 0) ^ 2 + (O 1 - P 1) ^ 2) := by
      rw [hC0, hC1]; ring
    rw [key, hOP, hlam]; field_simp; try ring
  have dBP : dist B P = M * (f * (2 * f ^ 2 - e ^ 2)) := by rw [dist_comm]; exact h12
  -- the triangles
  let Δ : Tri := triOf B P C hcrBPC
  let T2 : Tri := triOf B O C hcrBOC
  have hs2 : HasSides T2 (M * (f * (f ^ 2 - e ^ 2))) (M * (e * (2 * f ^ 2 - e ^ 2))) (M * f ^ 3) :=
    ⟨Equiv.refl _, dOC, dCB, h20⟩
  obtain ⟨E1, hE1c, hE1m⟩ := transport D1 T2 (congruent_of_hasSides_both h1t hs2)
  have hmod : E1.model.Congruent D2.model := by
    rw [hE1m]; exact congruent_of_hasSides_both h1m h2m
  let E1' := remodel E1 D2.model hmod
  have hE1't : E1'.target = E1.target := rfl
  have cov := fan_cover B P C O t ht0 ht1 hOt
  have dis := fan_disjoint B P C O t ht0 ht1 hOt hcrBPC
  have hT2c : T2.carrier = convexHull ℝ {B, O, C} := carrier_triOf _ _ _ hcrBOC
  have hΔc : Δ.carrier = convexHull ℝ {B, P, C} := carrier_triOf _ _ _ hcrBPC
  have hD2c : D2.target.carrier = convexHull ℝ {B, P, O} := by
    unfold Tri.carrier
    rw [range_perm D2.target τ, ← hO, ← hP, ← hB, set_perm_hull]
  have hcov : E1'.target.carrier ∪ D2.target.carrier = Δ.carrier := by
    rw [hE1't, hE1c, hT2c, hD2c, hΔc, cov, Set.union_comm]
  have hdisj : Disjoint (interior E1'.target.carrier) (interior D2.target.carrier) := by
    rw [hE1't, hE1c, hT2c, hD2c]; exact dis.symm
  refine ⟨_root_.unionCongruentDissection Δ E1' D2 rfl hcov hdisj, ?_, ?_⟩
  · let σ : Equiv.Perm (Fin 3) := ⟨![2, 0, 1], ![1, 2, 0], fun x => by fin_cases x <;> rfl,
      fun x => by fin_cases x <;> rfl⟩
    refine ⟨σ, ?_, ?_, ?_⟩
    · show dist B P = _
      exact dBP
    · show dist P C = _
      exact dPC
    · show dist C B = _
      exact dCB
  · exact h2m

end Erdos634.Draft.ThetaComposeGlue

#print axioms Erdos634.Draft.ThetaComposeGlue.glue_cevian
