-- Draft/ThetaUnitStep.lean -- THE UNIT THETA STEP as a theorem about `CongruentDissection`s with target sides.
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
**`thetaTiled_step`.**  For `f * f = e * e + b` and `e < f`, put `T_t := theta_t(e,f)`: the isosceles triangle with legs
`t b f` and base `t b e` (apex angle alpha, base angles alpha + beta), the target of `ThetaCompose.theta_exists`
(there `t = j (2 f^2 - e^2)`).  `ThetaTiled e f b t` says: there is a `CongruentDissection` into `b t^2` copies of the
tile `(e f, b, f^2)` whose target has sides `(t b f, t b f, t b e)`.

  `thetaTiled_step :  e >= 1 -> e < f -> f*f = e*e + b -> e <= (f-e) * n -> ThetaTiled e f b n -> ThetaTiled e f b (n+1)`.

No coprimality is used.  The new tiling contains the old one as the homothetic corner block at a base vertex and adds
`b (2n+1)` tiles in two ladder trapezoids (`ThetaUnitCore`, `ThetaUnitAssemble`).

CREDIT: the annulus / band steps on a seed are D. Paliy's (2026-10-08, prior art for the method); the families are
Yan Zhang's; the skew frame is Beeson-Rosu's; `ThetaCompose` (the seed theorem `theta_exists`), `LadderFam`, `CollarLayer`
are this project's.  The unit step: internal notes 2026-11-14 (T1), checked by exact arithmetic in internal audit.
INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaUnitAssemble
import Erdos634.Draft.ThetaCompose

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaUnit
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.CollarFam
open Erdos634.Draft.FDBBaseBetaE1 (HasSides hasSides_rot hasSides_swap)
open Erdos634.Draft.DebtB (sqf hasSides_triC_base hasSides_triC_o1 hasSides_triC_o2)

/-- **`theta_t(e,f)` is tiled.**  A `CongruentDissection` into `b t^2` copies of the tile `(e f, b, f^2)` (`b = f^2 - e^2`)
whose target is the isosceles triangle with legs `t b f` and base `t b e`.  (Same target and model data as
`ThetaCompose.theta_exists`, which has `t = j (2 f^2 - e^2)`.) -/
def ThetaTiled (e f b t : ℕ) : Prop :=
  ∃ D : CongruentDissection (b * t * t),
    HasSides D.target ((t : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * f) ((t : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * f)
      ((t : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * e) ∧
    HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)

/-- the model brick of the row has the sides of the tile -/
theorem mrow_hasSides {φ : ℝ} (hφ : 1 < φ) (e f : ℕ) (he : 0 < e) (hef : e < f) (hφE : φ = (f : ℝ) / e) :
    HasSides (Mrow hφ e f he hef) ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2) := by
  have hE : (0 : ℝ) < e := by exact_mod_cast he
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  obtain ⟨hb0, ha0, hc0⟩ := pos_facts hE hEF
  have hF : (0 : ℝ) < f := by linarith
  subst hφE
  have h := hasSides_triC_o1 hφ ((0 : ℝ), (0 : ℝ)) (((f : ℝ) ^ 2 - (e : ℝ) ^ 2), 0)
    (((f : ℝ) ^ 2 - (e : ℝ) ^ 2), (e : ℝ) * f) (by intro h; nlinarith [mul_pos hb0 ha0])
    (x := (f : ℝ) ^ 2 - (e : ℝ) ^ 2) (y := (e : ℝ) * f) (z := (f : ℝ) ^ 2) hb0.le ha0.le hc0.le
    (by simp only [sqf]; ring) (by simp only [sqf]; ring)
    (by simp only [sqf]; field_simp; ring)
  exact hasSides_swap h

/-- **THE UNIT THETA STEP.**  If `theta_n(e,f)` is tiled and `(f-e) n >= e`, then `theta_{n+1}(e,f)` is tiled (by
`b (n+1)^2` copies of the same tile).  Coprimality is not needed. -/
theorem thetaTiled_step (e f b n : ℕ) (he : 1 ≤ e) (hef : e < f) (hb : f * f = e * e + b)
    (hg : e ≤ (f - e) * n) (h : ThetaTiled e f b n) : ThetaTiled e f b (n + 1) := by
  obtain ⟨D, hDt, hDm⟩ := h
  have he0 : 0 < e := he
  have hE : (0 : ℝ) < e := by exact_mod_cast he0
  have hEF : (e : ℝ) < f := by exact_mod_cast hef
  have hF : (0 : ℝ) < f := by linarith
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · subst h0; simp at hg; omega
    · exact h0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have : ((f * f : ℕ) : ℝ) = ((e * e + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  obtain ⟨hb0, ha0, hc0⟩ := pos_facts hE hEF
  have hφ : 1 < (f : ℝ) / e := by rw [lt_div_iff₀ hE]; linarith
  set φ : ℝ := (f : ℝ) / e with hφdef
  set E : ℝ := (e : ℝ) with hEdef
  set F : ℝ := (f : ℝ) with hFdef
  set nR : ℝ := (n : ℝ) with hnRdef
  -- the old target as a triangle of the frame
  have hdet0 : ((tA1 E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tA2 E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) -
      ((tA2 E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tA1 E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) ≠ 0 := by
    have : ((tA1 E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tA2 E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) -
        ((tA2 E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tA1 E F nR).2 - ((0 : ℝ), (0 : ℝ)).2)
        = (F * (F ^ 2 - E ^ 2) * nR) * (E * (F ^ 2 - E ^ 2) * nR) := by
      dsimp only [tA1, tA2]; ring
    rw [this]; exact (mul_pos (mul_pos (mul_pos hF hb0) hnR) (mul_pos (mul_pos hE hb0) hnR)).ne'
  have hN0 : (0 : ℝ) < nR + 1 := by linarith
  have hdetT : ((tO E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tB E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) -
      ((tB E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tO E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) ≠ 0 := by
    have : ((tO E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tB E F nR).2 - ((0 : ℝ), (0 : ℝ)).2) -
        ((tB E F nR).1 - ((0 : ℝ), (0 : ℝ)).1) * ((tO E F nR).2 - ((0 : ℝ), (0 : ℝ)).2)
        = (F * (F ^ 2 - E ^ 2) * (nR + 1)) * (E * (F ^ 2 - E ^ 2) * (nR + 1)) := by
      dsimp only [tO, tB]; ring
    rw [this]; exact (mul_pos (mul_pos (mul_pos hF hb0) hN0) (mul_pos (mul_pos hE hb0) hN0)).ne'
  let T0 : Erdos634.Geometry.Tri := triC φ hφ ((0 : ℝ), (0 : ℝ)) (tA1 E F nR) (tA2 E F nR) hdet0
  let T1 : Erdos634.Geometry.Tri := triC φ hφ ((0 : ℝ), (0 : ℝ)) (tO E F nR) (tB E F nR) hdetT
  -- side data of the two triangles: (leg, leg, base) = (|BC|, |AB|, |CA|)
  have hs0 : HasSides T0 (F * (F ^ 2 - E ^ 2) * nR) (F * (F ^ 2 - E ^ 2) * nR) (E * (F ^ 2 - E ^ 2) * nR) := by
    refine hasSides_triC_o2 hφ _ _ _ hdet0 (by positivity) (by positivity) (by positivity) ?_ ?_ ?_ <;>
      (simp only [sqf, tA1, tA2, hφdef]; field_simp; ring)
  have hs1 : HasSides T1 (F * (F ^ 2 - E ^ 2) * (nR + 1)) (F * (F ^ 2 - E ^ 2) * (nR + 1))
      (E * (F ^ 2 - E ^ 2) * (nR + 1)) := by
    refine hasSides_triC_o2 hφ _ _ _ hdetT (by positivity) (by positivity) (by positivity) ?_ ?_ ?_ <;>
      (simp only [sqf, tO, tB, hφdef]; field_simp; ring)
  -- transport the old tiling onto T0
  have hDt' : HasSides D.target (F * (F ^ 2 - E ^ 2) * nR) (F * (F ^ 2 - E ^ 2) * nR) (E * (F ^ 2 - E ^ 2) * nR) :=
    Erdos634.Draft.UniformThreshold.hasSides_congr hDt (by ring) (by ring) (by ring)
  obtain ⟨E1, hE1c, hE1m⟩ := Erdos634.Draft.CVCCevianCut.transport D T0
    (Erdos634.Draft.ThetaComposeGlue.congruent_of_hasSides_both hDt' hs0)
  have hmod : E1.model.Congruent (Mrow hφ e f he0 hef) := by
    rw [hE1m]
    exact Erdos634.Draft.ThetaComposeGlue.congruent_of_hasSides_both hDm (mrow_hasSides hφ e f he0 hef rfl)
  have R0 : RTiling (thetaSet φ E F nR) (Mrow hφ e f he0 hef) (b * n * n) :=
    { tile := E1.tile
      covers := E1.covers.trans (hE1c.trans (carrier_triC _ _ _ _ _ _))
      disj := E1.interiors_disjoint
      cong := fun i => (E1.tiles_congruent i).trans hmod }
  obtain ⟨R1⟩ := step_rtiling hφ e f b n he0 hef hb rfl hg R0
  have R1' : RTiling T1.carrier (Mrow hφ e f he0 hef) (b * (n + 1) * (n + 1)) := by
    rw [show T1.carrier = thetaNext φ E F nR from carrier_triC _ _ _ _ _ _]; exact R1
  refine ⟨toCD R1', ?_, ?_⟩
  · show HasSides T1 _ _ _
    refine Erdos634.Draft.UniformThreshold.hasSides_congr hs1 ?_ ?_ ?_ <;> (push_cast; ring)
  · exact mrow_hasSides hφ e f he0 hef rfl

end

end Erdos634.Draft.ThetaUnit
