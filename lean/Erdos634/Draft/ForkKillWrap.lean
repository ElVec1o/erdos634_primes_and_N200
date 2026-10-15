import Erdos634.OrderForcing

/-!
# Fork kill and the A₂ branch: arithmetic kernels (wrapper)

`OrderForcing.lean` contains the five arithmetic lemmas used for the fork kill and the A₂ branch:

* `straight_junction_cases`: the two multiplicity distributions at a straight junction.
* `straight_junction_gamma_bound`: at most one γ at a straight junction.
* `east_cover_gap`: the east-cover count equation has no solution.
* `alpha_vertex_gap`: the α-vertex gap (n·f+1 ≠ K·f², e=1 version).
* `anti_brick_side`: the anti-brick squared third side misses every tile side.

The brick/mate configuration objects (the row fork, the A₂ branch, the block/mate
lattice) have no Dissection-level definition in Lean; only these arithmetic kernels are stated.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.ForkKillWrap

open Erdos634.OrderForcing

/-- Junction case split: the only multiplicity distributions at a straight junction. -/
theorem fork_junction_cases (na nb ng : ℕ)
    (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) :=
  straight_junction_cases na nb ng h1 h2

/-- At most one γ meets a straight junction. -/
theorem fork_junction_gamma_bound (na nb ng : ℕ)
    (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) : ng ≤ 1 :=
  straight_junction_gamma_bound na nb ng h1 h2

/-- The east-cover gap: the east-cover count equation x·f + y·(f²−1) + z·f² = f²−1−f has no ℕ solution. -/
theorem a2_east_cover_gap {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f) : False :=
  east_cover_gap hf h

/-- The α-vertex gap (e=1): n·f+1 ≠ K·f². -/
theorem fork_alpha_vertex_gap {f n K : ℕ} (hf : 2 ≤ f)
    (h : n * f + 1 = K * (f * f)) : False :=
  alpha_vertex_gap hf h

/-- The anti-brick side: f⁴−2f²+2 is not a², b², or c². -/
theorem fork_anti_brick_side {f : ℕ} (hf : 2 ≤ f) :
    (f * f) * (f * f) - 2 * (f * f) + 2 ≠ f * f ∧
    (f * f) * (f * f) - 2 * (f * f) + 2 ≠ (f * f - 1) * (f * f - 1) ∧
    (f * f) * (f * f) - 2 * (f * f) + 2 ≠ (f * f) * (f * f) :=
  anti_brick_side hf

/-- Non-vacuity: all parameter hypotheses are satisfiable. -/
theorem fork_witness :
    ∃ (na nb ng : ℕ), na + 2 * ng = 3 ∧ nb + ng = 2 :=
  ⟨3, 2, 0, by norm_num, by norm_num⟩

#print axioms fork_junction_cases
#print axioms fork_junction_gamma_bound
#print axioms a2_east_cover_gap
#print axioms fork_alpha_vertex_gap
#print axioms fork_anti_brick_side

end Erdos634.Draft.ForkKillWrap
