-- Draft/ThetaNotchE1.lean -- COROLLARY N1: for e = 1, `theta_t(1,f)` is tiled IFF `t >= 2 f` (every f >= 2).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
YES half: `ThetaNotchInst.thetaTiled_e1` (the notch seed `NP` at `m = j = 1`, `s = f+1`, plus the unit-step up-set `ThetaUnitUp`).
NO half: `ThetaKill.theta_e1` (S9 of this project, a different, previous proof).  Both halves have the SAME targets and the SAME model:
the isosceles triangle with legs `t f (f^2-1)` and base `t (f^2-1)`, the tile `(f, f^2-1, f^2)`, any number of tiles,
reflections allowed (`CongruentDissection`).
CREDIT: Paliy (annulus / band steps on a seed), Beeson (the 48 seed, `f = 2`), Laczkovich, Zhang.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotchInst
import Erdos634.Draft.ThetaKill

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled)

/-- **Corollary N1 (iff).**  For every `f >= 2` and `t >= 1`: `theta_t(1,f)` is tiled by the tile `(f, f^2-1, f^2)` if and only if `t >= 2 f`. -/
theorem thetaTiled_e1_iff (f : ℕ) (hf : 2 ≤ f) (t : ℕ) (ht : 0 < t) : ThetaTiled 1 f (f * f - 1) t ↔ 2 * f ≤ t := by
  constructor
  · rintro ⟨D, hT, hM⟩
    have h1 : 1 ≤ f * f := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have hb : ((f * f - 1 : ℕ) : ℝ) = (f : ℝ) ^ 2 - 1 := by rw [Nat.cast_sub h1]; push_cast; ring
    have := Erdos634.Draft.ThetaKill.theta_e1 D (t := (t : ℤ)) (f := (f : ℤ)) (by exact_mod_cast hf) (by exact_mod_cast ht)
      (Erdos634.Draft.UniformThreshold.hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring))
      (Erdos634.Draft.UniformThreshold.hasSides_congr hM (by push_cast; ring) (by push_cast; ring) (by push_cast; ring))
    exact_mod_cast this.1
  · exact thetaTiled_e1 f hf t

end

end Erdos634.Draft.ThetaNotch
