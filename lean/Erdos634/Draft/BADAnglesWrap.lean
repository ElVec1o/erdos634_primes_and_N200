import Erdos634.BADAngles

namespace Erdos634.Draft.BADAnglesWrap

open Erdos634.BADL2
open Erdos634.Geometry

noncomputable section

/-- Delegation: `ang_bounds`. -/
theorem wrap_ang_bounds (T : Tri) (k : Fin 3) :
    0 ≤ T.angleAt k ∧ T.angleAt k ≤ Real.pi :=
  ang_bounds T k

/-- Delegation: `cos_laws`. -/
theorem wrap_cos_laws (T : Tri) :
    2 * T.oppLen 1 * T.oppLen 2 * Real.cos (T.angleAt 0)
        = T.oppLen 1 ^ 2 + T.oppLen 2 ^ 2 - T.oppLen 0 ^ 2 ∧
    2 * T.oppLen 2 * T.oppLen 0 * Real.cos (T.angleAt 1)
        = T.oppLen 2 ^ 2 + T.oppLen 0 ^ 2 - T.oppLen 1 ^ 2 ∧
    2 * T.oppLen 0 * T.oppLen 1 * Real.cos (T.angleAt 2)
        = T.oppLen 0 ^ 2 + T.oppLen 1 ^ 2 - T.oppLen 2 ^ 2 :=
  cos_laws T

/-- Delegation: `tile_angles` — the four angle conclusions for a tile with sides `(ef, f²-e², f²)`. -/
theorem wrap_tile_angles (T : Tri) (σ : Equiv.Perm (Fin 3)) (e f : ℤ) (h0 : 0 < e) (hef : e < f)
    (hl0 : T.oppLen (σ 0) = (e : ℝ) * f)
    (hl1 : T.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hl2 : T.oppLen (σ 2) = (f : ℝ) ^ 2) :
    Real.cos (T.angleAt (σ 0)) = (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) / (2 * (f : ℝ) ^ 2) ∧
    3 * T.angleAt (σ 0) + 2 * T.angleAt (σ 1) = Real.pi ∧
    T.angleAt (σ 2) = Real.pi - T.angleAt (σ 0) - T.angleAt (σ 1) ∧
    ¬∃ r : ℚ, T.angleAt (σ 0) = r * Real.pi :=
  tile_angles T σ e f h0 hef hl0 hl1 hl2

example : True := trivial

#print axioms wrap_tile_angles

end

end Erdos634.Draft.BADAnglesWrap
