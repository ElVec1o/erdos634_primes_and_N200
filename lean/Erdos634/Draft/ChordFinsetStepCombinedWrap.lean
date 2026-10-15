import Erdos634.ChordFinsetStepCombined
namespace Erdos634.Draft.ChordFinsetStepCombinedWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_gap_free_of_finset_step' {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q p r s : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (R S : Fin N → Plane) {m : Fin N} (T : Finset (Fin N))
    (hpr : p ≠ r)
    (hgom : Wbtw ℝ P r s) (ho : Wbtw ℝ p r s) (hle_m : Wbtw ℝ P p r)
    (hmtrace : (D.tile m).carrier ∩ {x | f x = c} = segment ℝ r s)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (hmin : ∀ k ∈ T,
      (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      dist P r ≤ dist P (R k))
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      k ∉ T → Wbtw ℝ P (S k) p) :
    ∀ k : Fin N, ∀ y ∈ openSegment ℝ p r, y ∉ interior (D.tile k).carrier :=
  gap_free_of_finset_step' D f hf c hPQ R S T hpr hgom ho hle_m hmtrace hglobal hmin hexcl

example : True := trivial
#print axioms gap_free_of_finset_step'
end Erdos634.Draft.ChordFinsetStepCombinedWrap
