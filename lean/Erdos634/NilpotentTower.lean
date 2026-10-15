import Mathlib.GroupTheory.Nilpotent

/-!
# No higher nilpotent layer

The content is pure group theory.  For a group `G`, if the lower central series satisfies
`γ_{n+1} = γ_n` at some `n`, then `γ_k = γ_n` for every `k ≥ n`.  For the tiling group the class-2
layer collapses (`γ₂ = γ₃`), so the tower has no further layers and every nilpotent quotient of `G`
equals its abelianization.

**Formalized here:** the general algebraic fact (`lcs_eventually_const`,
`no_layer_past_class_two`), for any group.  It needs no hypothesis about `n = 2`.  Since
`lcs(n+1) = ⁅lcs(n), ⊤⁆`, the equation `lcs(n) = lcs(n+1)` says that `lcs(n)` is a fixed point of
`X ↦ ⁅X,⊤⁆`, and a fixed point stays fixed under further application of the same map.

**Not formalized here:** that the tiling group's `γ₂ = γ₃` holds, which is a separate fact about a
specific group.
-/

namespace Erdos634.NilpotentTower

/-- **The lower central series is eventually constant once it stabilizes for one step.**
If `Subgroup.lowerCentralSeries G (n+1) = Subgroup.lowerCentralSeries G n`, then `Subgroup.lowerCentralSeries G m =
Subgroup.lowerCentralSeries G n` for every `m ≥ n`. Pure group theory; no hypothesis on `n` beyond the
one-step collapse. -/
theorem lcs_eventually_const {G : Type*} [Group G] {n : ℕ}
    (h : Subgroup.lowerCentralSeries G (n + 1) = Subgroup.lowerCentralSeries G n) :
    ∀ m ≥ n, Subgroup.lowerCentralSeries G m = Subgroup.lowerCentralSeries G n := by
  intro m hm
  induction m with
  | zero =>
    have hn0 : n = 0 := by omega
    subst hn0
    rfl
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hkn : k ≥ n := by omega
      have hk : Subgroup.lowerCentralSeries G k = Subgroup.lowerCentralSeries G n := ih hkn
      rw [Subgroup.lowerCentralSeries_succ, hk, ← Subgroup.lowerCentralSeries_succ, h]
    · have : n = k + 1 := by omega
      rw [this]

/-- **`rem:nilptower`'s exact statement, from the class-2 collapse.** If `γ₂ = γ₃`
(`Subgroup.lowerCentralSeries G 2 = Subgroup.lowerCentralSeries G 3`), then `γ_k = γ₂` for every `k ≥ 2` — the tower
has no layer past class 2. -/
theorem no_layer_past_class_two {G : Type*} [Group G]
    (h : Subgroup.lowerCentralSeries G 3 = Subgroup.lowerCentralSeries G 2) :
    ∀ k ≥ 2, Subgroup.lowerCentralSeries G k = Subgroup.lowerCentralSeries G 2 :=
  lcs_eventually_const h

/-- Non-vacuity: in an abelian group, `Subgroup.lowerCentralSeries G 1 = ⊥` already (the commutator subgroup
is trivial), so certainly `γ₂ = γ₃ = ⊥`, and the theorem applies with a genuine (trivial) witness. -/
example {G : Type*} [CommGroup G] : Subgroup.lowerCentralSeries G 3 = Subgroup.lowerCentralSeries G 2 := by
  have h1 : Subgroup.lowerCentralSeries G 1 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, Subgroup.lowerCentralSeries_zero]
    simp only [Subgroup.mem_top, true_and, Subgroup.closure_eq_bot_iff]
    rintro y ⟨x, x1, rfl⟩
    rw [commutatorElement_def, mul_comm x x1]
    show x1 * x * x⁻¹ * x1⁻¹ = 1
    group
  have h2 : Subgroup.lowerCentralSeries G 2 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, h1]
    simp
  have h3 : Subgroup.lowerCentralSeries G 3 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_succ, h2]
    simp
  rw [h2, h3]

end Erdos634.NilpotentTower

#print axioms Erdos634.NilpotentTower.lcs_eventually_const
#print axioms Erdos634.NilpotentTower.no_layer_past_class_two
