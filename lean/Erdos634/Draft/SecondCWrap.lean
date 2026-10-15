import Erdos634.SecondEdge

/-!
# Every admissible angular order ends in α: arithmetic kernel

On an equal side, the admissible angular orders all end
in α; hence the second edge is c (since α lays b or c, and equal sides carry no b).

Key arithmetic facts in `SecondEdge.lean`:

1. **`admissible_ends_alpha`**: among all 16 orderings of the two straight figures,
   every admissible one ends in α. Kernel-checked by `decide`.
2. **`admissible_exactly_two`**: exactly two orderings are admissible — non-vacuity.
3. **`second_edge_is_c`**: α lays b or c; no b on an equal side ⟹ edge = c.
4. **`n_c_ge_two`**: n_c + p·e = f and n_c ≥ 2 ⟹ p·e + 2 ≤ f (count consequence).

That the figure at J is one of the two straight figures and that T₁ presents β
are placement statements about the junction tile and are not part of this module.

0 sorry, [propext].
-/

namespace Erdos634.Draft.SecondCWrap

open Erdos634.Walls13 Erdos634.SecondEdge

/-- thm:secondc (core): every admissible angular order ends in α.
    Checks all 16 orderings of {α,β,γ} straight figures. -/
theorem secondc_admissible_ends_alpha :
    ((ordersABG ++ ordersAAABB).filter admissible).all
      (fun L => L.getLast? == some Angle.alpha) = true :=
  admissible_ends_alpha

/-- Non-vacuity: exactly two orders are admissible. -/
theorem secondc_exactly_two_admissible :
    (ordersABG ++ ordersAAABB).filter admissible
      = [[.beta, .gamma, .alpha], [.beta, .beta, .alpha, .alpha, .alpha]] :=
  admissible_exactly_two

/-- thm:secondc (corollary): α at boundary lays b or c. -/
theorem secondc_alpha_lays_bc {E : Edge}
    (hlay : E = (flanks Angle.alpha).1 ∨ E = (flanks Angle.alpha).2) :
    E = Edge.b ∨ E = Edge.c :=
  alpha_lays_b_or_c hlay

/-- thm:secondc (second edge): α lays b or c + no b on equal side ⟹ edge = c. -/
theorem secondc_second_edge_is_c {E : Edge}
    (hlay : E = (flanks Angle.alpha).1 ∨ E = (flanks Angle.alpha).2)
    (hnob : E ≠ Edge.b) : E = Edge.c :=
  second_edge_is_c hlay hnob

/-- Count consequence: n_c + p·e = f, n_c ≥ 2 ⟹ p·e + 2 ≤ f. -/
theorem secondc_n_c_count {n_c p e f : ℕ} (hside : n_c + p * e = f) (h2 : 2 ≤ n_c) :
    p * e + 2 ≤ f :=
  n_c_ge_two hside h2

#print axioms secondc_admissible_ends_alpha
#print axioms secondc_second_edge_is_c

end Erdos634.Draft.SecondCWrap
