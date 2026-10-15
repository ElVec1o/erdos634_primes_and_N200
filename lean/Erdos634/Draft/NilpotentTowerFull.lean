/-
Draft/NilpotentTowerFull.lean -- `rem:nilptower` (obstructions paper), the group-theoretic statement at the paper's
indices, and its consequence for nilpotent quotients.

Paper indexing: `γ₁ = G`, `γ₂ = [G, G]`, `γ_{k+1} = [G, γ_k]`.  Mathlib: `lowerCentralSeries G 0 = ⊤`,
`lowerCentralSeries G 1 = commutator G`, so `γ_k = Subgroup.lowerCentralSeries G (k − 1)`.
* `class_two_collapse`: if `γ₂ = γ₃` then `γ_k = γ₂` for every `k ≥ 2`.
  (`NilpotentTower.no_layer_past_class_two` has the hypothesis `lowerCentralSeries G 3 = Subgroup.lowerCentralSeries G 2`, which is
  the paper's `γ₄ = γ₃`: one index too high for the remark.)
* `nilpotent_quotient_abelian`: under the same hypothesis every nilpotent quotient `G ⧸ N` is abelian
  (`commutator G ≤ N`), i.e. it is a quotient of the abelianization.
* `collapse_witness`: the hypothesis holds in every abelian group (non-vacuity).

The premise for the tiling group itself (a computation in finite quotients, Remark OM-tilinggroup) is not a theorem of
the paper and is not formalized; the remark is stated conditionally. not prime-case work.  No sorry, no native_decide.
-/
import Mathlib
import Erdos634.NilpotentTower

namespace Erdos634.Draft.NilpotentTowerFull

/-- **If `γ₂ = γ₃` then `γ_k = γ₂` for all `k ≥ 2`** (paper indices). -/
theorem class_two_collapse {G : Type*} [Group G]
    (h : Subgroup.lowerCentralSeries G 2 = Subgroup.lowerCentralSeries G 1) :
    ∀ k ≥ 1, Subgroup.lowerCentralSeries G k = Subgroup.lowerCentralSeries G 1 :=
  Erdos634.NilpotentTower.lcs_eventually_const (n := 1) h

/-- **Under `γ₂ = γ₃` every nilpotent quotient is abelian.** -/
theorem nilpotent_quotient_abelian {G : Type*} [Group G]
    (h : Subgroup.lowerCentralSeries G 2 = Subgroup.lowerCentralSeries G 1)
    (N : Subgroup G) [N.Normal] (hnil : Group.IsNilpotent (G ⧸ N)) : _root_.commutator G ≤ N := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hnil
  have hmap := Subgroup.lowerCentralSeries.map (QuotientGroup.mk' N) n
  rw [hn] at hmap
  have hle : Subgroup.lowerCentralSeries G n ≤ N := by
    intro x hx
    have hx' : (QuotientGroup.mk' N) x ∈ (⊥ : Subgroup (G ⧸ N)) := hmap (Subgroup.mem_map_of_mem _ hx)
    rw [Subgroup.mem_bot] at hx'
    exact (QuotientGroup.eq_one_iff x).mp hx'
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · subst h0
    rw [Subgroup.lowerCentralSeries_zero] at hle
    exact le_trans le_top hle
  · rw [class_two_collapse h n h0, Subgroup.lowerCentralSeries_one] at hle
    exact hle

/-- Non-vacuity: the hypothesis holds in every abelian group. -/
theorem collapse_witness {G : Type*} [CommGroup G] :
    Subgroup.lowerCentralSeries G 2 = Subgroup.lowerCentralSeries G 1 := by
  have h1 : Subgroup.lowerCentralSeries G 1 = ⊥ := by
    rw [Subgroup.lowerCentralSeries_one, commutator_eq_bot_iff_center_eq_top]
    exact CommGroup.center_eq_top
  have h2 : Subgroup.lowerCentralSeries G 2 ≤ Subgroup.lowerCentralSeries G 1 := Subgroup.lowerCentralSeries_antitone (by norm_num)
  rw [h1] at h2 ⊢
  exact le_bot_iff.mp h2

end Erdos634.Draft.NilpotentTowerFull

#print axioms Erdos634.Draft.NilpotentTowerFull.class_two_collapse
#print axioms Erdos634.Draft.NilpotentTowerFull.nilpotent_quotient_abelian
#print axioms Erdos634.Draft.NilpotentTowerFull.collapse_witness
