import Erdos634.ChordFinsetGeometricChain
namespace Erdos634.Draft.ChordFinsetGeometricChainWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_exists_geometric_chain {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ)
    {P Q : Plane} (hPQ : D.target.carrier ∩ {x | f x = c} = segment ℝ P Q)
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧ R k ≠ S k ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k)) :
    ∀ (L : List (Fin N)), L.Nodup → ∀ (bound : Plane), Wbtw ℝ P bound Q →
      (∀ k ∈ L, (∃ a, f ((D.tile k).pts a) < c) ∧ (∃ b, c < f ((D.tile k).pts b))) →
      (∀ k ∈ L, Wbtw ℝ P bound (R k)) →
      (∀ k ∈ L, bound ≠ R k) →
      (∀ i j, (hi : i < L.length) → (hj : j < L.length) → i ≤ j →
        Wbtw ℝ P (R (L.get ⟨i, hi⟩)) (R (L.get ⟨j, hj⟩))) →
      (L.Pairwise (fun k l => k ≠ l →
        (segment ℝ (R k) (S k) ∩ segment ℝ (R l) (S l)).Subsingleton)) →
      (L.Pairwise (fun k l => R k ≠ R l ∧ R k ≠ S l ∧ S k ≠ R l ∧ S k ≠ S l)) →
      (∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
        k ∉ L → Wbtw ℝ P (S k) bound) →
      ∃ g : ℕ → Plane, g 0 = bound ∧
        (∀ i, i + 2 ≤ 2 * L.length → Wbtw ℝ (g i) (g (i + 1)) (g (i + 2))) ∧
        (∀ i, i ≤ 2 * L.length → g i ∈ D.target.carrier ∩ {x | f x = c}) ∧
        (∀ i (h : i < L.length),
          g (2 * i + 1) = R (L.get ⟨i, h⟩) ∧ g (2 * i + 2) = S (L.get ⟨i, h⟩)) ∧
        (∀ i, i ≤ L.length → ∀ k : Fin N, ∀ y ∈ openSegment ℝ (g (2 * i)) (g (2 * i + 1)),
          y ∉ interior (D.tile k).carrier) :=
  exists_geometric_chain D f hf c hPQ R S hglobal

example : True := trivial
#print axioms exists_geometric_chain
end Erdos634.Draft.ChordFinsetGeometricChainWrap
