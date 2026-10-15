-- Draft/FluxCBoundaryWitness.lean: non-vacuity witness for the triangle-target boundary lemma
-- (Draft/FluxCBoundary.lean) on the 44-tiling (`Tiling44Bridge.dissection`), which is not
-- edge-to-edge (`FluxWitness.tiling44_T_junction`).  Imported by `All`.
--
-- Every hypothesis of `CongruentDissection.triangle_boundary` / `_anchor` is exhibited: the model
-- `(16,24,32)` has angles `(β, γ, α)` in `L = ℤπ + ℤθ` (`FluxGridWitness.model_angles_mem`), the
-- target `(176,128,128)` has angles `(β, β, 3α)` in `L` (`target_angles_mem`), both characters are
-- `±1` (`rank2_sq`), and the anchor `0` is the direction of the target's base (`t_leftUnit0_angle`).
-- Evaluated through the lemma, with the target side read off corner angles and sides alone:
-- `K_{χ₊}(P) = −80`, `K_{χ₋}(P) = 432`, `s_0(P) = +1`, hence `S₊ = 2`, `S₋ = 6`, i.e. `K = −S₊ = −2`
-- and `M = S₋ = 6` in `Row12.flux_identities`.  `FluxRow11Witness` obtains the same numbers from the
-- flux directly.
import Erdos634.Draft.FluxCBoundary
import Erdos634.Draft.FluxGridWitness

open scoped Classical

namespace Erdos634.Draft.FluxCBoundaryWitness

open Erdos634.Geometry Erdos634.Tiling44Bridge Erdos634.Draft.FluxGridWitness
open Erdos634.Draft.FluxWitness

theorem hβ : β44 = ((2 : ℤ) : ℝ) * Real.pi + ((-3 : ℤ) : ℝ) * θ44 := β44_eq

theorem h3α : 3 * α44 = ((-3 : ℤ) : ℝ) * Real.pi + ((6 : ℤ) : ℝ) * θ44 := by
  unfold θ44; push_cast; ring

theorem t_ext2' : Real.pi - targetTri.angleAt (0 + 2)
    = ((4 : ℤ) : ℝ) * Real.pi + ((-6 : ℤ) : ℝ) * θ44 := t_ext2

/-- `K_{χ}(P)` for the target, from its angles `(β, β, 3α)` and sides `(128, 128, 176)`. -/
theorem paperK_target (b : ZMod 2) :
    (GridChar.rank2 θ44 θ44_irr b 0).paperK targetTri
      = -((if ((2 : ℤ) : ZMod 2) + b * ((-3 : ℤ) : ZMod 2) = 0 then 1 else -1) * 256
          + (if ((-3 : ℤ) : ZMod 2) + b * ((6 : ℤ) : ZMod 2) = 0 then 1 else -1) * 176) := by
  unfold GridChar.paperK
  rw [Fin.sum_univ_three, t_angle0, t_angle1, t_angle2, hβ, h3α, GridChar.rank2_chi,
    GridChar.rank2_chi, t_opp.1, t_opp.2.1, t_opp.2.2]
  ring

theorem paperK_target_plus : Gplus.paperK targetTri = -80 := by
  unfold Gplus; rw [paperK_target, if_pos (by decide), if_neg (by decide)]; norm_num

theorem paperK_target_minus : Gminus.paperK targetTri = 432 := by
  unfold Gminus; rw [paperK_target, if_neg (by decide), if_neg (by decide)]; norm_num

theorem paperK_model_plus : Gplus.paperK M44 = -40 := by
  rw [← Gplus.tileValue_eq_paperK (GridChar.rank2_sq _ _ _ _) M44 (model_angles_mem 0)]
  exact tileValue_plus

theorem paperK_model_minus : Gminus.paperK M44 = 72 := by
  rw [← Gminus.tileValue_eq_paperK (GridChar.rank2_sq _ _ _ _) M44 (model_angles_mem 1)]
  exact tileValue_minus

/-- The target's base sign `s_0(P) = χ(π − 3α)·F(base) = +1` for both characters. -/
theorem edgeSign_target (b : ZMod 2) :
    (GridChar.rank2 θ44 θ44_irr b 0).edgeSign targetTri 0 = 1 := by
  unfold GridChar.edgeSign
  rw [t_ext2', GridChar.rank2_chi, t_weight0, if_pos]
  · norm_num
  · have h4 : ((4 : ℤ) : ZMod 2) = 0 := by decide
    have h6 : ((-6 : ℤ) : ZMod 2) = 0 := by decide
    rw [h4, h6]; ring

/-- **The boundary lemma on the real 44-tiling, `χ₊`: `S₊ = 2`** (R12's `K = −2`). -/
theorem boundary_44_plus : ∃ S : ℤ, S = 2 ∧ (2 : ℤ) ∣ S - Tiling44.tiles.length
    ∧ |S| ≤ Tiling44.tiles.length := by
  obtain ⟨S, h2, hN, hk⟩ := dissection.triangle_boundary Gplus (GridChar.rank2_sq _ _ _ _)
    (model_angles_mem 0) (target_angles_mem 0)
  refine ⟨S, ?_, h2, hN⟩
  have e := hk 0
  change (S : ℝ) * Gplus.paperK M44 = Gplus.edgeSign targetTri 0 * Gplus.paperK targetTri at e
  rw [paperK_model_plus, paperK_target_plus, show Gplus.edgeSign targetTri 0 = 1 from
    edgeSign_target 0] at e
  have : (S : ℝ) = 2 := by linarith
  exact_mod_cast this

/-- **The boundary lemma on the real 44-tiling, `χ₋`: `S₋ = 6`** (R12's `M = 6`). -/
theorem boundary_44_minus : ∃ S : ℤ, S = 6 ∧ (2 : ℤ) ∣ S - Tiling44.tiles.length
    ∧ |S| ≤ Tiling44.tiles.length := by
  obtain ⟨S, h2, hN, hk⟩ := dissection.triangle_boundary Gminus (GridChar.rank2_sq _ _ _ _)
    (model_angles_mem 1) (target_angles_mem 1)
  refine ⟨S, ?_, h2, hN⟩
  have e := hk 0
  change (S : ℝ) * Gminus.paperK M44 = Gminus.edgeSign targetTri 0 * Gminus.paperK targetTri at e
  rw [paperK_model_minus, paperK_target_minus, show Gminus.edgeSign targetTri 0 = 1 from
    edgeSign_target 1] at e
  have : (S : ℝ) = 6 := by linarith
  exact_mod_cast this

/-- **The anchored form on the real 44-tiling** (anchor = base direction, `hanc` exhibited):
`S·K(model) = −χ(3α)·K(P)` gives `S₊ = 2` with no sign to evaluate. -/
theorem boundary_44_anchor_plus : ∃ S : ℤ, S = 2 ∧ (2 : ℤ) ∣ S - Tiling44.tiles.length := by
  obtain ⟨S, h2, -, e⟩ := dissection.triangle_boundary_anchor Gplus (GridChar.rank2_sq _ _ _ _)
    (model_angles_mem 0) (target_angles_mem 0) 0 t_leftUnit0_angle.symm
  refine ⟨S, ?_, h2⟩
  change (S : ℝ) * Gplus.paperK M44
    = - Gplus.chi ((targetTri.angleAt (0 + 2) : ℝ) : Real.Angle) * Gplus.paperK targetTri at e
  rw [paperK_model_plus, paperK_target_plus, show (0 : Fin 3) + 2 = 2 from rfl, t_angle2, h3α]
    at e
  unfold Gplus at e
  rw [GridChar.rank2_chi, if_neg (by decide)] at e
  have : (S : ℝ) = 2 := by linarith
  exact_mod_cast this

/-- **Sign check.**  The lemma's conclusion pins `S` exactly: on the same tiling the value
`S₊ = −2` (the other sign of the `±` form) is refuted by the explicit edge sign. -/
theorem boundary_44_plus_not_neg : ¬ ∃ S : ℤ, S = -2 ∧ ∀ k : Fin 3,
    (S : ℝ) * Gplus.paperK M44 = Gplus.edgeSign targetTri k * Gplus.paperK targetTri := by
  rintro ⟨S, rfl, hk⟩
  have e := hk 0
  rw [paperK_model_plus, paperK_target_plus, show Gplus.edgeSign targetTri 0 = 1 from
    edgeSign_target 0] at e
  norm_num at e

end Erdos634.Draft.FluxCBoundaryWitness

#print axioms Erdos634.Draft.FluxCBoundaryWitness.boundary_44_plus
#print axioms Erdos634.Draft.FluxCBoundaryWitness.boundary_44_minus
#print axioms Erdos634.Draft.FluxCBoundaryWitness.boundary_44_anchor_plus
#print axioms Erdos634.Draft.FluxCBoundaryWitness.boundary_44_plus_not_neg
