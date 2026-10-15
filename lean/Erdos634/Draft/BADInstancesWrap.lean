import Erdos634.BADInstances

namespace Erdos634.Draft.BADInstancesWrap

open LaurentPolynomial
open BAD

/-- Delegation: `witness_84` — the algebraic witness showing `Hyp` is satisfiable at `(e,f)=(1,2)`. -/
theorem wrap_witness_84 :
    Bdry 1 2 6 = tsum 1 2 [(6, -1, false), (8, -2, true), (-4, -2, false)] :=
  witness_84

/-- Delegation: `control_34` — no signed tile sum represents `Bdry 1 3 4`. -/
theorem wrap_control_34 (l : List (ℤ × ℤ × Bool)) : Bdry 1 3 4 ≠ tsum 1 3 l :=
  control_34 l

/-- Delegation: `N_form` — shared arithmetic: `b ∣ w` and `N b = w² Q` give `N = r² b Q`. -/
theorem wrap_N_form (b Q w N : ℤ) (hb : b ≠ 0) (hdiv : b ∣ w) (hN : N * b = w ^ 2 * Q) :
    ∃ r : ℤ, N = r ^ 2 * b * Q :=
  N_form b Q w N hb hdiv hN

/-- Delegation: `seven_rows` — all seven rows of `cor:basealphadiv` satisfy `good`. -/
theorem wrap_seven_rows : ∀ x ∈ rows, good x :=
  seven_rows

example : True := trivial

#print axioms wrap_control_34

end Erdos634.Draft.BADInstancesWrap
