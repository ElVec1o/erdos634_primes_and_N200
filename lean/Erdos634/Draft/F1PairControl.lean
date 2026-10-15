/-
Draft/F1PairControl.lean -- non-vacuity of `F1PairCert.F1Pair`.

On the certified 3240-tiling of the `F₁` triangle `(135, 315, 360)` by the `2π/3` tile `(3, 5, 7)`
(`G3CF1n3240`, Zhang's construction; control file `G3CF1nControl`) every hypothesis of `F1Pair 3240 36 90` holds:
`IrrPi α`, `TwoPiThreeData`, `F1Data` with `μ = 45`, and the pair equations `36 b = μ (c − a)`, `90 b = μ (c + a)`
(`36 · 90 = 3240`).  So `F1Pair N Ma Mb` is a statement about situations that occur, and it is false for this pair.

Composite-N control; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.G3CF1nControl
import Erdos634.Draft.F1PairCert

open scoped Classical

namespace Erdos634.Draft.F1PairCert

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.G3CF1nControl Erdos634.Draft.G3CAng
open Erdos634.Draft.G3CF1n3240 (cert cert_ok cert_len)

/-- the `F₁` data of the real 3240-tiling: target sides `45 · (a, c, a + b)` for the tile `(a, b, c) = 1890 · (3, 5, 7)` -/
theorem control_f1Data : D.target.F1Data α (1890 * 3) (1890 * 5) (1890 * 7) 45 := by
  have h2 : D.target.angleAt 2 = α := angle_eq_of_cos 2 (σm 0) (t_cos2.trans cos_α.symm)
  have hs := D.target.angleAt_sum
  refine ⟨by norm_num, Equiv.swap 0 2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Equiv.swap_apply_left, h2]; push_cast; ring
  · rw [Equiv.swap_apply_left, t_opp2]; norm_num
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), t_angle1]; push_cast; ring
  · rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide), t_opp1]; norm_num
  · rw [Equiv.swap_apply_right]; push_cast; linarith [t_angle1, h2]
  · rw [Equiv.swap_apply_right, t_opp0]; norm_num

/-- **Non-vacuity of `F1Pair`**: the pair `(36, 90)` of `N = 3240` is realized by a real dissection (the number of
tiles of the certified dissection is `cert.leaves.length = 3240`). -/
theorem f1Pair_control : cert.leaves.length = 3240 ∧ ¬ F1Pair cert.leaves.length 36 90 := by
  refine ⟨cert_len, fun h => ?_⟩
  exact h D α (1890 * 3) (1890 * 5) (1890 * 7) 45 α_irr data control_f1Data (by norm_num) (by norm_num)
    (by norm_num)

end Erdos634.Draft.F1PairCert

#print axioms Erdos634.Draft.F1PairCert.f1Pair_control
