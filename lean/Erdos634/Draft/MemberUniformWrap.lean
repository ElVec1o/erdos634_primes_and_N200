import Erdos634.MemberUniform

namespace Erdos634.Draft.MemberUniformWrap

open Erdos634.MemberUniform Erdos634.Geometry Real

theorem mu_fill_iff_counts {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (X Y x y z : ℕ) :
    ((x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = (X : ℝ) * α + (Y : ℝ) * β)
      ↔ (x + 2 * z = X ∧ y + z = Y) :=
  fill_iff_counts hrel hirr X Y x y z

theorem mu_gap_one_uniform (f f' : ℕ) (hf : 2 ≤ f) (hf' : 2 ≤ f') :
    (¬ ∃ x y z : ℕ, x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1) ∧
    (¬ ∃ x y z : ℕ, x * f' + y * (f' ^ 2 - 1) + z * f' ^ 2 = 1) :=
  gap_one_uniform f f' hf hf'

example : True := trivial

#print axioms mu_fill_iff_counts
#print axioms mu_gap_one_uniform

end Erdos634.Draft.MemberUniformWrap
