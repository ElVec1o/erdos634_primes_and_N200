-- Non-vacuity of the model hypothesis of `R1Final.r1_no_tiling` at every member: a coordinate triangle
-- with sides `(ef, f² − e², f²)` (side `j` opposite vertex `j`) exists for all real `0 < e < f`
-- (in particular every thick member `e = f − 1`).  `MarchCompose.modelTri` is the `e = 1` case.
-- Vertices `(f², 0)`, `(0, 0)`, `(x, y)` with `x = e²(3f² − e²)/(2f²)`,
-- `y = e(f² − e²)√(4f² − e²)/(2f²)`; the key identity is
-- `4f⁶ − e²(3f² − e²)² = (f² − e²)²(4f² − e²)`.
import Erdos634.Draft.R1Final

namespace Erdos634.Draft.R1TileWitness

open Erdos634.Geometry Erdos634.CertCoord Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord

/-- The apex abscissa. -/
noncomputable def tx (e f : ℝ) : ℝ := e ^ 2 * (3 * f ^ 2 - e ^ 2) / (2 * f ^ 2)
/-- The apex height. -/
noncomputable def ty (e f : ℝ) : ℝ :=
  e * (f ^ 2 - e ^ 2) * Real.sqrt (4 * f ^ 2 - e ^ 2) / (2 * f ^ 2)

theorem ty_pos {e f : ℝ} (he : 0 < e) (hef : e < f) : 0 < ty e f := by
  have hf : 0 < f := by linarith
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have h4 : 0 < 4 * f ^ 2 - e ^ 2 := by nlinarith
  unfold ty
  have := Real.sqrt_pos.mpr h4
  positivity

theorem ty_sq {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ty e f ^ 2 = e ^ 2 * (f ^ 2 - e ^ 2) ^ 2 * (4 * f ^ 2 - e ^ 2) / (4 * f ^ 4) := by
  have h4 : 0 ≤ 4 * f ^ 2 - e ^ 2 := by nlinarith
  unfold ty
  rw [div_pow, mul_pow, mul_pow, Real.sq_sqrt h4]
  ring

theorem det_tileTri {e f : ℝ} (he : 0 < e) (hef : e < f) :
    det3 (f ^ 2) 0 0 0 (tx e f) (ty e f) ≠ 0 := by
  have hf : 0 < f := by linarith
  have : det3 (f ^ 2) 0 0 0 (tx e f) (ty e f) = -(f ^ 2 * ty e f) := by unfold det3; ring
  rw [this]
  exact neg_ne_zero.mpr (mul_pos (by positivity) (ty_pos he hef)).ne'

/-- **The tile `(ef, f² − e², f²)`** in the `sideOpp` labelling. -/
noncomputable def tileTri (e f : ℝ) (he : 0 < e) (hef : e < f) : Tri :=
  mkTri (f ^ 2) 0 0 0 (tx e f) (ty e f) (det_tileTri he hef)

theorem tileTri_sides {e f : ℝ} (he : 0 < e) (hef : e < f) :
    sideOpp (tileTri e f he hef) 0 = e * f ∧
    sideOpp (tileTri e f he hef) 1 = f ^ 2 - e ^ 2 ∧
    sideOpp (tileTri e f he hef) 2 = f ^ 2 := by
  have hf : 0 < f := by linarith
  have hf2 : f ^ 2 ≠ 0 := by positivity
  have hb : 0 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have hty := ty_sq he hef
  simp only [sideOpp, tileTri, Erdos634.MarchKills.mkTri_pts₀, Erdos634.MarchKills.mkTri_pts₁,
    Erdos634.MarchKills.mkTri_pts₂]
  refine ⟨?_, ?_, ?_⟩
  · show dist (mkPt 0 0) (mkPt (tx e f) (ty e f)) = e * f
    refine Erdos634.MarchKillsFan.dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt, show (0 - tx e f) ^ 2 + (0 - ty e f) ^ 2 = tx e f ^ 2 + ty e f ^ 2 by ring,
      hty]
    unfold tx; field_simp; ring
  · show dist (mkPt (tx e f) (ty e f)) (mkPt (f ^ 2) 0) = f ^ 2 - e ^ 2
    refine Erdos634.MarchKillsFan.dist_eq_of_sq_eq ?_ dist_nonneg hb
    rw [dist_sq_mkPt, show (tx e f - f ^ 2) ^ 2 + (ty e f - 0) ^ 2
        = (tx e f - f ^ 2) ^ 2 + ty e f ^ 2 by ring, hty]
    unfold tx; field_simp; ring
  · show dist (mkPt (f ^ 2) 0) (mkPt 0 0) = f ^ 2
    refine Erdos634.MarchKillsFan.dist_eq_of_sq_eq ?_ dist_nonneg (by positivity)
    rw [dist_sq_mkPt]; ring

/-- **Non-vacuity of `r1_no_tiling`'s hypotheses at every thick member `e + 1 = f`, `f ≥ 2`**
(individually; jointly they are unsatisfiable, which is the theorem): the target congruence is
satisfiable (reflexivity), a triangle `T` with sides `(ef, f² − e², f²)` exists (`tileTri`), and the
model congruence is satisfiable (reflexivity). -/
theorem hyps_nonvacuous {e f : ℕ} (he : 1 ≤ e) (hef1 : e + 1 = f) :
    (baseBetaTarget e f (by exact_mod_cast (show 0 < e by omega))
        (by exact_mod_cast (show e < f by omega))).Congruent
      (baseBetaTarget e f (by exact_mod_cast (show 0 < e by omega))
        (by exact_mod_cast (show e < f by omega))) ∧
    ∃ T : Tri, sideOpp T 0 = (e : ℝ) * f ∧ sideOpp T 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      sideOpp T 2 = (f : ℝ) ^ 2 ∧ T.Congruent T := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast (show 0 < e by omega)
  have hefR : (e : ℝ) < f := by exact_mod_cast (show e < f by omega)
  obtain ⟨h0, h1, h2⟩ := tileTri_sides he0 hefR
  exact ⟨Tri.Congruent.refl _, tileTri e f he0 hefR, h0, h1, h2, Tri.Congruent.refl _⟩

end Erdos634.Draft.R1TileWitness

#print axioms Erdos634.Draft.R1TileWitness.det_tileTri
#print axioms Erdos634.Draft.R1TileWitness.tileTri_sides
#print axioms Erdos634.Draft.R1TileWitness.hyps_nonvacuous
