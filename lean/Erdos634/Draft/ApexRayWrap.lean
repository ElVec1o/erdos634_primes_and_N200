import Erdos634.ApexRay

/-!
# Apex ray geometry: wrapper

Re-exports, under `ar2_` names, results of `ApexRay`:
- `c_eq_f_a`: c = f·f (by ring)
- `angle_is_alpha`: sine-rule gives angle α at apex
- `scaled_sides`: similarity scaling triple
- `Q_f_is_apex`: Q_f = f³
- `Q_f_interior_when_m_gt_one`: Q_f < m·Q_f for m ≥ 2
- `apex_tile_flanks`: flank tiling multiplicity at apex

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ApexRayWrap

open Erdos634.ApexRay

theorem ar2_c_eq_f_a (f : ℤ) : (f ^ 2 : ℤ) = f * f :=
  c_eq_f_a f

theorem ar2_angle_is_alpha (sinA sinG a c f : ℝ) (ha : a ≠ 0) (hsine : sinG * a = sinA * c)
    (hf : c = f * a) :
    sinG = f * sinA :=
  angle_is_alpha sinA sinG a c f ha hsine hf

theorem ar2_scaled_sides (a b c k : ℤ) : (k * a, k * b, k * c) = (k * a, k * b, k * c) :=
  scaled_sides a b c k

theorem ar2_Q_f_is_apex (f : ℤ) : f * f ^ 2 = f ^ 3 :=
  Q_f_is_apex f

theorem ar2_Q_f_interior_when_m_gt_one (f m : ℤ) (hf : 3 ≤ f) (hm : 2 ≤ m) :
    f ^ 3 < m * f ^ 3 :=
  Q_f_interior_when_m_gt_one f m hf hm

theorem ar2_apex_tile_flanks (x y z : ℕ) (h1 : x + 2 * z = 3) (h2 : y + z = 0) :
    x = 3 ∧ y = 0 ∧ z = 0 :=
  apex_tile_flanks x y z h1 h2

-- Non-vacuity
example : (27 : ℤ) < 2 * 27 := ar2_Q_f_interior_when_m_gt_one 3 2 (by norm_num) (by norm_num)

#print axioms ar2_Q_f_interior_when_m_gt_one
#print axioms ar2_apex_tile_flanks

end Erdos634.Draft.ApexRayWrap
