/-
Draft/LayerE1Tools.lean

The base-β target `T_m` of the member `(1, f)` at the level of the frame `Φ_f`, in the style of `WAddF.WClosed`:

    def TClosed f hf m                -- `Φ_f '' DS (A m) (B m) (C m)` is cut into `(3f² − 1) m²` copies of `MF f`
    theorem DTriR_sq                  -- the three squared sides of `WtoDeltaF.DTriR`
    theorem DeltaTri_sides            -- `WtoDeltaF.DeltaTri f hf m`: legs `m f³`, base `(3f² − 1) m`
    theorem tcount                    -- a tiling of `T_m` by copies of `MF f` has `(3f² − 1) m²` tiles (area)
    theorem TClosed_of_dissection     -- a `CongruentDissection` with the sides of `T_m` and of the tile, ANY number
                                      --   of tiles, gives `TClosed f hf m`
    theorem TClosed_of_betaTilable    -- `BetaTilable 1 f m → TClosed f hf m`
    theorem betaTilable_of_TClosed    -- `TClosed f hf m → BetaTilable 1 f m`

`A = f (f² − 1)`, `B = 2f² − 1`, `C = 3f² − 1`; `DS u v w` is the triangle `(u, 0)`, `(u, w)`, `(0, v)` of
`Draft.WtoDeltaF`.  `BetaTilable` leaves the number of tiles free, so the number is recovered here from the area
relation `ARA.area_heron`.  The proofs are copies of `WClosedBase.WClosed_of_dissection` and
`WClosedBase.betaTilable_of_WClosed` with `W` replaced by `T`.

This file serves `Draft.LayerE1` (paper: `prop:layer`).  Nothing here is a construction.
No sorry, no native_decide.
-/
import Erdos634.Draft.WClosedBase
import Erdos634.ARAGeom

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)

namespace Erdos634.Draft.LayerE1
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF
open Erdos634.Draft.WPgramF Erdos634.Draft.WGridF Erdos634.Draft.WAddF Erdos634.Draft.WtoDeltaF
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap congruent_of_hasSides')
open Erdos634.Draft.UniformThreshold (BetaTilable hasSides_congr)

/-- T-closure: `T_m` of the member `(1, f)` (`m ≥ 1` natural), in the frame `Φ_f`, admits a tiling by `(3f² − 1) m²`
tiles congruent to `MF f`.  (The set is the carrier of `WtoDeltaF.DeltaTri f hf m`: `carrier_DeltaTri`.) -/
def TClosed (f : ℕ) (hf : 2 ≤ f) (m : ℕ) : Prop :=
  Nonempty (RTiling (Phi (f : ℝ) '' DS ((f : ℝ) * ((f : ℝ) ^ 2 - 1) * m) ((2 * (f : ℝ) ^ 2 - 1) * m)
      ((3 * (f : ℝ) ^ 2 - 1) * m))
    (MF (f : ℝ) (hF f hf)) ((3 * f ^ 2 - 1) * m ^ 2))

/-- the squared sides of the triangle `DTriR`: vertices `Φ(u, 0)`, `Φ(u, w)`, `Φ(0, v)`
(modelled on `WClosedBase.WTriR_sq`) -/
theorem DTriR_sq (F : ℝ) (hF1 : 1 < F) (u v w : ℝ) (hu : 0 < u) (hw : 0 < w) :
    dist ((DTriR F hF1 u v w hu hw).pts 1) ((DTriR F hF1 u v w hu hw).pts 2) ^ 2
      = u ^ 2 + (w - v) ^ 2 + u * (w - v) / F ∧
    dist ((DTriR F hF1 u v w hu hw).pts 2) ((DTriR F hF1 u v w hu hw).pts 0) ^ 2
      = u ^ 2 + v ^ 2 - u * v / F ∧
    dist ((DTriR F hF1 u v w hu hw).pts 0) ((DTriR F hF1 u v w hu hw).pts 1) ^ 2 = w ^ 2 := by
  simp only [DTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  refine ⟨?_, ?_, ?_⟩
  · rw [sq_Phi hF1]; simp only; ring
  · rw [sq_Phi hF1]; simp only; ring
  · rw [sq_Phi hF1]; simp only; ring

/-- the sides of `T_m` in the frame: legs `m f³`, base `(3f² − 1) m`
(the three computations of `WClosedBase.betaTilable_of_WClosed`, verbatim) -/
theorem DeltaTri_sides (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) :
    dist ((DeltaTri f hf m hm).pts 1) ((DeltaTri f hf m hm).pts 2) = (m : ℝ) * (f : ℝ) ^ 3 ∧
    dist ((DeltaTri f hf m hm).pts 2) ((DeltaTri f hf m hm).pts 0) = (m : ℝ) * (f : ℝ) ^ 3 ∧
    dist ((DeltaTri f hf m hm).pts 0) ((DeltaTri f hf m hm).pts 1) = (3 * (f : ℝ) ^ 2 - 1) * m := by
  have hF1 := hF f hf
  have hF0 : (f : ℝ) ≠ 0 := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  refine ⟨?_, ?_, ?_⟩
  · simp only [DeltaTri, DTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi hF1]; simp only; field_simp; ring
  · simp only [DeltaTri, DTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine (sq_eq_sq₀ dist_nonneg (by positivity)).mp ?_
    rw [sq_Phi hF1]; simp only; field_simp; ring
  · simp only [DeltaTri, DTriR, triC_pts, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    refine (sq_eq_sq₀ dist_nonneg (mul_pos (hC_pos f hf) hm0).le).mp ?_
    rw [sq_Phi hF1]; simp only; ring

/-- the sides opposite the vertices `0, 1, 2` (definitional; as in `ARA.four_det_sq`) -/
theorem oppLen_eq (T : Erdos634.Geometry.Tri) : T.oppLen 0 = dist (T.pts 1) (T.pts 2) ∧ T.oppLen 1 = dist (T.pts 2) (T.pts 0) ∧
    T.oppLen 2 = dist (T.pts 0) (T.pts 1) :=
  ⟨rfl, rfl, rfl⟩

/-- **The number of tiles of `T_m`.**  A tiling of the frame triangle `T_m` by `N` copies of `MF f` has
`N = (3f² − 1) m²`: the area relation in Heron form (`ARA.area_heron`),
`N² (f² − 1)² (4f² − 1) = ((3f² − 1) m²)² (f² − 1)² (4f² − 1)`. -/
theorem tcount (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) {N : ℕ}
    (R : RTiling (DeltaTri f hf m hm).carrier (MF (f : ℝ) (hF f hf)) N) : N = (3 * f ^ 2 - 1) * m ^ 2 := by
  have hF1 := hF f hf
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hF1
  obtain ⟨t12, t20, t01⟩ := DeltaTri_sides f hf m hm
  obtain ⟨D, hDT, hDM⟩ : ∃ D : CongruentDissection N,
      D.target = DeltaTri f hf m hm ∧ D.model = MF (f : ℝ) hF1 :=
    ⟨toCD (T := DeltaTri f hf m hm) R, rfl, rfl⟩
  have h := Erdos634.ARA.area_heron D
  rw [hDM, hDT] at h
  obtain ⟨a0, a1, a2⟩ := oppLen_eq (MF (f : ℝ) hF1)
  obtain ⟨b0, b1, b2⟩ := oppLen_eq (DeltaTri f hf m hm)
  have e0 : (MF (f : ℝ) hF1).oppLen 0 = (f : ℝ) := by rw [a0]; exact m2
  have e1 : (MF (f : ℝ) hF1).oppLen 1 = (f : ℝ) ^ 2 := by rw [a1, dist_comm]; exact m3
  have e2 : (MF (f : ℝ) hF1).oppLen 2 = (f : ℝ) ^ 2 - 1 := by rw [a2]; exact m1
  have g0 : (DeltaTri f hf m hm).oppLen 0 = (m : ℝ) * (f : ℝ) ^ 3 := by rw [b0]; exact t12
  have g1 : (DeltaTri f hf m hm).oppLen 1 = (m : ℝ) * (f : ℝ) ^ 3 := by rw [b1]; exact t20
  have g2 : (DeltaTri f hf m hm).oppLen 2 = (3 * (f : ℝ) ^ 2 - 1) * m := by rw [b2]; exact t01
  rw [e0, e1, e2, g0, g1, g2] at h
  unfold Erdos634.ARA.Hh at h
  have hP : (0 : ℝ) < ((f : ℝ) ^ 2 - 1) ^ 2 * (4 * (f : ℝ) ^ 2 - 1) :=
    mul_pos (pow_pos (hA_pos hF1) 2) (by nlinarith)
  have hK : (0 : ℝ) ≤ (3 * (f : ℝ) ^ 2 - 1) * (m : ℝ) ^ 2 := mul_nonneg (hC_pos f hf).le (sq_nonneg _)
  -- both Heron polynomials are multiples of `(f²−1)²(4f²−1)`
  have hz : ((N : ℝ) ^ 2 - ((3 * (f : ℝ) ^ 2 - 1) * (m : ℝ) ^ 2) ^ 2)
      * (((f : ℝ) ^ 2 - 1) ^ 2 * (4 * (f : ℝ) ^ 2 - 1)) = 0 := by
    linear_combination h
  have hsq : (N : ℝ) ^ 2 = ((3 * (f : ℝ) ^ 2 - 1) * (m : ℝ) ^ 2) ^ 2 := by
    rcases mul_eq_zero.mp hz with h0 | h0
    · linarith
    · exact absurd h0 hP.ne'
  have hN : (N : ℝ) = (3 * (f : ℝ) ^ 2 - 1) * (m : ℝ) ^ 2 := (sq_eq_sq₀ (Nat.cast_nonneg N) hK).mp hsq
  have h1 : 1 ≤ 3 * f ^ 2 := by nlinarith
  have hcast : (N : ℝ) = (((3 * f ^ 2 - 1) * m ^ 2 : ℕ) : ℝ) := by
    rw [hN, Nat.cast_mul, Nat.cast_sub h1]; push_cast; ring
  exact_mod_cast hcast

/-- **A dissection with the sides of `T_m` and of the tile gives `TClosed f m`**; the number of tiles is not assumed
(copy of `WClosedBase.WClosed_of_dissection`). -/
theorem TClosed_of_dissection (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) {N : ℕ} (D : CongruentDissection N)
    (hT : HasSides D.target ((m : ℝ) * (f : ℝ) ^ 3) ((m : ℝ) * (f : ℝ) ^ 3) ((3 * (f : ℝ) ^ 2 - 1) * m))
    (hM : HasSides D.model (f : ℝ) ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - 1)) : TClosed f hf m := by
  have hF1 := hF f hf
  obtain ⟨t12, t20, t01⟩ := DeltaTri_sides f hf m hm
  have hTU : D.target.Congruent (DeltaTri f hf m hm) :=
    Erdos634.Draft.FDBBaseBetaE1.congruent_of_hasSides hT t12 t20 t01
  obtain ⟨g, D', hD'T, hD'M, -⟩ := Erdos634.NormalPosition.exists_normal_position_congruent D hTU
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hF1
  have hMF : D.model.Congruent (MF (f : ℝ) hF1) := congruent_of_hasSides' hM m1 m2 m3
  have R : RTiling (DeltaTri f hf m hm).carrier (MF (f : ℝ) hF1) N :=
    { tile := D'.tile
      covers := by rw [D'.covers, hD'T]
      disj := D'.interiors_disjoint
      cong := fun i => (D'.tiles_congruent i).trans (by rw [hD'M]; exact hMF) }
  have hN := tcount f hf m hm R
  exact ⟨RTiling.castN hN (RTiling.cast (carrier_DeltaTri f hf m hm) R)⟩

/-- a tiling of the base-β target of `(1, f)` at scale `m`, in the frame -/
theorem TClosed_of_betaTilable (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) (h : BetaTilable 1 f m) :
    TClosed f hf m := by
  obtain ⟨N, D, hT, hM⟩ := h
  refine TClosed_of_dissection f hf m hm D ?_ ?_
  · exact hasSides_congr hT (by ring) (by ring) (by push_cast; ring)
  · exact hasSides_congr (hasSides_rot (hasSides_swap hM)) (by push_cast; ring) (by ring) (by push_cast; ring)

/-- **`TClosed f m` gives the base-β target at scale `m`** (member `(1, f)`), in the form of
`UniformThreshold.BetaTilable` (copy of `WClosedBase.betaTilable_of_WClosed`). -/
theorem betaTilable_of_TClosed (f : ℕ) (hf : 2 ≤ f) (m : ℕ) (hm : 1 ≤ m) (hW : TClosed f hf m) :
    BetaTilable 1 f m := by
  have hF1 := hF f hf
  obtain ⟨R⟩ := hW
  obtain ⟨D, hT, hM⟩ : ∃ D : CongruentDissection ((3 * f ^ 2 - 1) * m ^ 2),
      D.target = DeltaTri f hf m hm ∧ D.model = MF (f : ℝ) hF1 :=
    ⟨toCD (T := DeltaTri f hf m hm) (RTiling.cast (carrier_DeltaTri f hf m hm).symm R), rfl, rfl⟩
  obtain ⟨m1, m2, m3⟩ := Erdos634.Draft.WPgramWrap.MF_sides hF1
  obtain ⟨t12, t20, t01⟩ := DeltaTri_sides f hf m hm
  have hTs : HasSides D.target ((m : ℝ) * (f : ℝ) ^ 3) ((m : ℝ) * (f : ℝ) ^ 3) ((3 * (f : ℝ) ^ 2 - 1) * m) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hT]; exact t12,
      by simp only [Equiv.refl_apply]; rw [hT]; exact t20,
      by simp only [Equiv.refl_apply]; rw [hT]; exact t01⟩
  have hMs : HasSides D.model (f : ℝ) ((f : ℝ) ^ 2) ((f : ℝ) ^ 2 - 1) :=
    ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; rw [hM]; exact m2,
      by simp only [Equiv.refl_apply]; rw [hM, dist_comm]; exact m3,
      by simp only [Equiv.refl_apply]; rw [hM]; exact m1⟩
  exact ⟨_, D, hasSides_congr hTs (by ring) (by ring) (by push_cast; ring),
    hasSides_congr (hasSides_rot (hasSides_swap hMs)) (by push_cast; ring) (by push_cast; ring) (by ring)⟩

end Erdos634.Draft.LayerE1

#print axioms Erdos634.Draft.LayerE1.tcount
#print axioms Erdos634.Draft.LayerE1.TClosed_of_dissection
#print axioms Erdos634.Draft.LayerE1.TClosed_of_betaTilable
#print axioms Erdos634.Draft.LayerE1.betaTilable_of_TClosed
