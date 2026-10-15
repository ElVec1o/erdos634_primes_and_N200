import Erdos634.ChordFinsetChainInj

namespace Erdos634.Draft.ChordFinsetChainInjWrap
open Erdos634.ChordTraceReal

theorem wrap_exists_injective_chain {Plane : Type*} :
    ∀ (L : List (Plane × Plane)) (bound : Plane),
      (∀ pr ∈ L, pr.1 ≠ pr.2) →
      (∀ pr ∈ L, bound ≠ pr.1 ∧ bound ≠ pr.2) →
      (L.Pairwise (fun pr1 pr2 => pr1.1 ≠ pr2.1 ∧ pr1.1 ≠ pr2.2 ∧ pr1.2 ≠ pr2.1 ∧ pr1.2 ≠ pr2.2)) →
      ∃ g : ℕ → Plane, g 0 = bound ∧
        (∀ a b, a ≤ 2 * L.length → b ≤ 2 * L.length → a ≠ b → g a ≠ g b) ∧
        ∀ i (h : i < L.length), g (2 * i + 1) = (L.get ⟨i, h⟩).1 ∧
          g (2 * i + 2) = (L.get ⟨i, h⟩).2 :=
  exists_injective_chain

example : True := trivial
#check @wrap_exists_injective_chain

end Erdos634.Draft.ChordFinsetChainInjWrap
