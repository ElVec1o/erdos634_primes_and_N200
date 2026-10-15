-- Draft/SIXCong.lean
-- SSS in the form used by the reflective bridges: matching opposite-side lengths up to a vertex permutation.
import Erdos634.SssCongruent
import Erdos634.Draft.FluxTurn

namespace Erdos634.Geometry
namespace SIX

theorem third_index : ∀ (π : Equiv.Perm (Fin 3)) (i j : Fin 3), i ≠ j →
    ∃ k : Fin 3, ((k + 1 = i ∧ k + 2 = j) ∨ (k + 1 = j ∧ k + 2 = i)) ∧
      ((π k + 1 = π i ∧ π k + 2 = π j) ∨ (π k + 1 = π j ∧ π k + 2 = π i)) := by decide

/-- If the side opposite vertex `k` of `T` has the length of the side opposite vertex `π k` of `U`, then `T ≅ U`. -/
theorem cong_of_oppLens (T U : Tri) (π : Equiv.Perm (Fin 3)) (h : ∀ k, T.oppLen k = U.oppLen (π k)) :
    T.Congruent U := by
  refine Erdos634.SssCongruent.congruent_of_dist_perm π (fun i j => ?_)
  by_cases hij : i = j
  · subst hij; simp
  · obtain ⟨k, hk1, hk2⟩ := third_index π i j hij
    have h' := h k
    unfold Tri.oppLen at h'
    rcases hk1 with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hk2 with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
      simp only [e1, e2, f1, f2] at h' <;> simpa [dist_comm] using h'

/-- Same, with the vertex correspondence given as `σ` on `T`'s side and `κ` on `U`'s. -/
theorem cong_of_oppLens_sigma (T U : Tri) (σ κ : Equiv.Perm (Fin 3))
    (h : ∀ j, T.oppLen (σ j) = U.oppLen (κ j)) : T.Congruent U :=
  cong_of_oppLens T U (σ.symm.trans κ) (fun k => by
    obtain ⟨j, rfl⟩ := σ.surjective k
    simpa using h j)

end SIX
end Erdos634.Geometry

#print axioms Erdos634.Geometry.SIX.cong_of_oppLens_sigma
