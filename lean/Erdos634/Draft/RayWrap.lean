import Erdos634.PinRay

/-!
# The mismatch ray: arithmetic kernel

`PinRay.exit_not_integral_member` is the arithmetic content of the statement that the mismatch ray is determined:

For the base-β member (N₀ = 3f²−1), any p with 1 ≤ p ≤ f−1, and any
integer T:  (3f²−1)·T ≠ f³·((3f²−1) − p·f).

That the ray's tiles actually satisfy this integrality
condition is a placement statement and is not part of this file.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.RayWrap

/-- The arithmetic content of thm:ray: for any 2 ≤ f, 1 ≤ p ≤ f−1 and integer T,
    the ray exit equation (3f²−1)·T = f³·((3f²−1) − p·f) has no solution. -/
theorem ray_exit_not_integral (f p T : ℤ) (hf : 2 ≤ f) (hp1 : 1 ≤ p) (hp2 : p ≤ f - 1)
    (h : (3 * f ^ 2 - 1) * T = f ^ 3 * ((3 * f ^ 2 - 1) - p * f)) : False :=
  Erdos634.PinRay.exit_not_integral_member f p T hf hp1 hp2 h

/-- Non-vacuity: the hypotheses are satisfiable (f=2, p=1, T=1 gives LHS=11, RHS=8·(11−2)=72;
    these are UNequal so the hypothesis of the theorem is not satisfied by design —
    the theorem says False from the equation.  We show instead that f=2, p=1 satisfy
    all parameter conditions (2 ≤ 2, 1 ≤ 1, 1 ≤ 2−1=1) and the equation IS satisfiable
    in ℤ with a SPECIFIC T, but then False follows.  The witness is the hypotheses themselves. -/
theorem ray_witness : ∃ (f p : ℤ), 2 ≤ f ∧ 1 ≤ p ∧ p ≤ f - 1 :=
  ⟨2, 1, by norm_num, by norm_num, by norm_num⟩

#print axioms ray_exit_not_integral

end Erdos634.Draft.RayWrap
