/-
Draft/B3PrimeWitness.lean -- control for `B3Prime.s5_shape` on the REAL 48-tile atom.

`FDCCevianAtom.atomTiles_four_scaled` is an exact dissection of the triangle `(24, 24, 12)` into 48 copies of
`(2, 3, 4)`: a target with angles `(α+β, α+β, α)`.  `control_shape_A4`: all hypotheses of `s5_shape` (irrationality of
`α/π`, `3α + 2β = π`, the model data, the target angles) hold on this dissection, and the theorem returns integers
`t, e, f` with `#tiles = t² (f² − e²)` and the γ-trap words.  So `s5_shape`, the only geometric input of `b3prime`, is
not vacuous; `b3prime` itself then needs `N` prime, which fails here (`#tiles = 48`).

No sorry, no native_decide.
-/
import Erdos634.Draft.B3Prime
import Erdos634.Draft.S5Family
import Erdos634.Draft.FDCCevianAtom

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1 Erdos634.Draft.TheoremPConditional

open Erdos634.Geometry.GapE120Dis in
theorem control_shape_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    HasSides D.target 24 24 12 ∧ HasSides D.model 2 3 4 ∧
    ∃ t e f : ℤ, 0 < t ∧ 0 < e ∧ e < f ∧ IsCoprime e f ∧
      ((G3CAtomTiling.tiles.length : ℕ) : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) ∧
      S5Word t e f e ∧ S5Word t e f f := by
  obtain ⟨D, h1, h2⟩ := Erdos634.Draft.FDCCevianAtom.atomTiles_four_scaled
  have hT : HasSides D.target 24 24 12 := hasSides_rot h1
  refine ⟨D, hT, h2, ?_⟩
  obtain ⟨τ, a1, a2, a3⟩ := hT
  obtain ⟨σ, m1, m2, m3⟩ := h2
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  obtain ⟨hirr, hrel, hmod, hP0, hP1⟩ := s5_angles (t := 4) (e := 1) (f := 2) (by norm_num) (by norm_num)
    (by norm_num) (D.relabelTarget' τ) (by rw [show (D.relabelTarget' τ).target.oppLen 0 = _ from a1]; norm_num)
    (by rw [show (D.relabelTarget' τ).target.oppLen 1 = _ from a2]; norm_num)
    (by rw [show (D.relabelTarget' τ).target.oppLen 2 = _ from a3]; norm_num) σ
    (by rw [show (D.relabelTarget' τ).model.oppLen (σ 0) = _ from s1.symm.trans m1]; norm_num)
    (by rw [show (D.relabelTarget' τ).model.oppLen (σ 1) = _ from s2.symm.trans ((dist_comm _ _).trans m2)]; norm_num)
    (by rw [show (D.relabelTarget' τ).model.oppLen (σ 2) = _ from s3.symm.trans m3]; norm_num)
  have hP2 : (D.relabelTarget' τ).target.angleAt 2 = (D.relabelTarget' τ).model.angleAt (σ 0) := by
    have := (D.relabelTarget' τ).target.angleAt_sum
    rw [hP0, hP1] at this
    linarith
  exact s5_shape (D.relabelTarget' τ) hirr hrel hmod ⟨Equiv.refl _, hP0, hP1, hP2⟩

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.control_shape_A4
