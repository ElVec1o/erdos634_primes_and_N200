import Erdos634.ChordFinsetWrapper
namespace Erdos634.Draft.ChordFinsetWrapperWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_exists_geometric_chain_of_finset {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧ R k ≠ S k ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (T : Finset (Fin N)) (bound : Plane) (hPb : Wbtw ℝ P bound Q)
    (hmem : ∀ k ∈ T, (∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b)))
    (hle : ∀ k ∈ T, Wbtw ℝ P bound (R k)) (hbne : ∀ k ∈ T, bound ≠ R k)
    (hcross : ∀ k ∈ T, ∀ l ∈ T, k ≠ l →
      (segment ℝ (R k) (S k) ∩ segment ℝ (R l) (S l)).Subsingleton)
    (hptcross : ∀ k ∈ T, ∀ l ∈ T, k ≠ l →
      R k ≠ R l ∧ R k ≠ S l ∧ S k ≠ R l ∧ S k ≠ S l)
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      k ∉ T → Wbtw ℝ P (S k) bound) :
    ∃ g : ℕ → Plane, g 0 = bound ∧
      (∀ i, i + 2 ≤ 2 * T.card → Wbtw ℝ (g i) (g (i + 1)) (g (i + 2))) ∧
      (∀ i, i ≤ 2 * T.card → g i ∈ D.target.carrier ∩ {x | f x = c}) ∧
      (∀ i, i < T.card → ∃ t : Fin N,
        (D.tile t).carrier ∩ {x | f x = c} = segment ℝ (g (2 * i + 1)) (g (2 * i + 2))) ∧
      (∀ i, i ≤ T.card → ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g (2 * i)) (g (2 * i + 1)),
        y ∉ interior (D.tile k).carrier) :=
  exists_geometric_chain_of_finset D f hf c hPQ R S hglobal T bound hPb hmem hle hbne
    hcross hptcross hexcl

example : True := trivial
#print axioms exists_geometric_chain_of_finset
end Erdos634.Draft.ChordFinsetWrapperWrap
