import Erdos634.NilpotentTower

/-!
# Nilpotent tower: no layer past class 2

If the lower central series of a group satisfies γ₂ = γ₃, then γ_k = γ₂ for all k ≥ 2.

`NilpotentTower.no_layer_past_class_two` is exactly this statement: it is general, quantified over any
group, and does not mention the tiling group.  `NilpotentTower.lcs_eventually_const` is the key lemma it rests on.

The condition γ₂ = γ₃ is a hypothesis of the theorem; it is not asserted here for any tiling group.

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.NilpotentTowerWrap

/-- If γₙ = γₙ₊₁ then γ_m = γₙ for all m ≥ n (general group theory). -/
theorem lcs_const_from_step {G : Type*} [Group G] {n : ℕ}
    (h : Subgroup.lowerCentralSeries G (n + 1) = Subgroup.lowerCentralSeries G n) :
    ∀ m ≥ n, Subgroup.lowerCentralSeries G m = Subgroup.lowerCentralSeries G n :=
  Erdos634.NilpotentTower.lcs_eventually_const h

/-- No layer past class 2: if γ₂ = γ₃ then γ_k = γ₂ for all k ≥ 2 (general group theory). -/
theorem no_layer_past_class_two {G : Type*} [Group G]
    (h : Subgroup.lowerCentralSeries G 3 = Subgroup.lowerCentralSeries G 2) :
    ∀ k ≥ 2, Subgroup.lowerCentralSeries G k = Subgroup.lowerCentralSeries G 2 :=
  Erdos634.NilpotentTower.no_layer_past_class_two h

-- Non-vacuity: NilpotentTower.lean has a verified `example` for CommGroup G showing γ₂ = γ₃.
-- Not duplicated here. The hypothesis is satisfiable.

#print axioms lcs_const_from_step
#print axioms no_layer_past_class_two

end Erdos634.Draft.NilpotentTowerWrap
