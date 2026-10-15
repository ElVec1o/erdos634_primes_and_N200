import Erdos634.OrderForcing

/-!
# Mirrored-piece charge, arithmetic kernel

A mirrored cover piece is charged: it forces a second `{β,3γ}` climber
vertex (v₁ ≥ 2).

The arithmetic content has two steps, both in `OrderForcing.lean`:

1. `mirrored_left_junction`: a mirrored piece's left junction satisfies `n_β ≥ 2`, which forces
   the figure `{3α,2β}` (a straight figure of type n₂). Given the junction balance equations and
   `nb ≥ 2`, we get `na = 3`, `nb = 2`, `ng = 0`.

2. `escape_charge`: given n₂ ≥ 1 (at least one {3α,2β} junction) and the vertex census balance
   equations, then v₁ ≥ 2 (at least two {β,3γ} climber vertices).

The statement that a tile is a mirrored cover piece needs the brick/mate row structure, which has no
`Dissection`-level definition in this file.

No sorry; both steps are `omega` arguments, with standard axioms from imports.
-/

namespace Erdos634.Draft.LemChargeWrap

open Erdos634.OrderForcing

/-- A mirrored left junction with nb ≥ 2 forces the figure {3α, 2β}. -/
theorem mirrored_piece_junction {na nb ng : ℕ}
    (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) (hb : 2 ≤ nb) :
    na = 3 ∧ nb = 2 ∧ ng = 0 :=
  mirrored_left_junction na nb ng h1 h2 hb

/-- With n₂ ≥ 1 (a {3α,2β} junction exists) and the census balance, v₁ ≥ 2. -/
theorem mirrored_piece_forces_second_climber {N n1 n2 v1 v2 v3 v4 : ℕ}
    (hn2 : 1 ≤ n2)
    (ha : 3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N)
    (hb : 2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N)
    (hg : n1 + 3 * v1 + 2 * v2 + v3 = N) : 2 ≤ v1 :=
  escape_charge hn2 ha hb hg

/-- Non-vacuity: n₂ = 1 and the simplest non-trivial census is satisfiable. -/
theorem charge_witness :
    ∃ N n1 n2 v1 v2 v3 v4 : ℕ,
      1 ≤ n2 ∧
      3 + n1 + 3 * n2 + 2 * v2 + 4 * v3 + 6 * v4 = N ∧
      2 + n1 + 2 * n2 + v1 + 2 * v2 + 3 * v3 + 4 * v4 = N ∧
      n1 + 3 * v1 + 2 * v2 + v3 = N := by
  -- With n2=1, v1=2, all others 0: ha: 3+0+3=6=N; hb: 2+0+2+2=6=N; hg: 0+6=6=N. N=6.
  exact ⟨6, 0, 1, 2, 0, 0, 0, by norm_num, by norm_num, by norm_num, by norm_num⟩

#print axioms mirrored_piece_junction
#print axioms mirrored_piece_forces_second_climber

end Erdos634.Draft.LemChargeWrap
