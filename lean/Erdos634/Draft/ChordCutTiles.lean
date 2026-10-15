/-
Draft/ChordCutTiles.lean  In `AllThreshold`.

`ChordCut.restrict_below` with the extra conclusion that every tile of the sub-dissection is a tile of the original one
(needed to carry a wall from `D` to `D'`: a segment that meets no interior point of a tile of `D` meets none of `D'`).
Same hypotheses, same proof (copied from `ChordCut.restrict_below`, which is not edited); the extra conclusion is
`SubDissection.restrictCongruent_tile = rfl`.

    restrict_below_tiles   -- `∃ N' D', D'.target = T' ∧ D'.model = D.model ∧ ∀ j, ∃ i, D'.tile j = D.tile i`

Non-vacuity: the hypotheses are those of `ChordCut.restrict_below`, which `ChordCutWitness.restrict_above_witness`
satisfies by a real dissection (and `restrict_below_tiles` for the other side of the same wall is obtained the same way).
No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.ChordCut

open scoped Classical
set_option linter.unusedVariables false
open Erdos634.Geometry Erdos634.ChordTraceReal

namespace Erdos634.Draft.ChordCutTiles
open Erdos634.Draft.ChordCut (not_straddles_of_empty)

theorem restrict_below_tiles {N : ℕ} (D : CongruentDissection N) (g : Plane →ₗ[ℝ] ℝ) (hg : g ≠ 0) (c : ℝ)
    (h0 : straddlers D.toDissection g c = ∅) (T' : Erdos634.Geometry.Tri)
    (hT' : T'.carrier = D.target.carrier ∩ {y | g y ≤ c}) :
    ∃ (N' : ℕ) (D' : CongruentDissection N'), D'.target = T' ∧ D'.model = D.model ∧
      ∀ j, ∃ i, D'.tile j = D.tile i := by
  obtain ⟨S, hmemS⟩ : ∃ S : Finset (Fin N), ∀ i, i ∈ S ↔ ∀ x ∈ (D.tile i).carrier, g x ≤ c :=
    ⟨Finset.univ.filter (fun i => ∀ x ∈ (D.tile i).carrier, g x ≤ c), fun i => by simp⟩
  have hUclosed : IsClosed (⋃ i ∈ S, (D.tile i).carrier) :=
    isClosed_biUnion_finset (fun i _ => (D.tile i).isCompact.isClosed)
  have hbelow : ∀ i x, x ∈ (D.tile i).carrier → g x < c → i ∈ S := by
    intro i x hx hgx
    rcases Erdos634.ChordTraceReal.Tri.sign_trichotomy (D.tile i) g c with h | h | h
    · exact (hmemS i).mpr h
    · exact absurd (h x hx) (not_le.mpr hgx)
    · exact absurd h (not_straddles_of_empty D.toDissection g c h0 i)
  have hlt : ∀ y ∈ interior T'.carrier, g y < c := by
    intro y hy
    have hy' : y ∈ T'.carrier := interior_subset hy
    have hle : g y ≤ c := by
      rw [hT'] at hy'
      exact hy'.2
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      have hv : ∀ j, g (T'.pts j) ≤ c := by
        intro j
        have hj : T'.pts j ∈ T'.carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
        rw [hT'] at hj
        exact hj.2
      obtain ⟨_, ⟨i, hi⟩⟩ := interior_on_line_straddles T' g hg c hy h
      exact absurd (hv i) (not_le.mpr hi)
  have hint_sub : interior T'.carrier ⊆ ⋃ i ∈ S, (D.tile i).carrier := by
    intro y hy
    have hy' : y ∈ T'.carrier := interior_subset hy
    have hyt : y ∈ D.target.carrier := by
      rw [hT'] at hy'
      exact hy'.1
    rw [← D.covers] at hyt
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hyt
    exact Set.mem_iUnion₂.mpr ⟨i, hbelow i y hi (hlt y hy), hi⟩
  have hcl : T'.carrier ⊆ closure (interior T'.carrier) := by
    have h := T'.convex.closure_interior_eq_closure_of_nonempty_interior T'.interior_nonempty
    rw [h, T'.isCompact.isClosed.closure_eq]
  have hcov : (⋃ i ∈ S, (D.tile i).carrier) = T'.carrier := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨i, hiS, hxi⟩ := Set.mem_iUnion₂.mp hx
      rw [hT']
      exact ⟨tile_subset_target D.toDissection i hxi, (hmemS i).mp hiS x hxi⟩
    · intro x hx
      exact hUclosed.closure_subset_iff.mpr hint_sub (hcl hx)
  exact ⟨S.card, Erdos634.SubDissection.restrictCongruent D S T' hcov, rfl, rfl,
    fun j => ⟨S.orderEmbOfFin rfl j, rfl⟩⟩

end Erdos634.Draft.ChordCutTiles

#print axioms Erdos634.Draft.ChordCutTiles.restrict_below_tiles
