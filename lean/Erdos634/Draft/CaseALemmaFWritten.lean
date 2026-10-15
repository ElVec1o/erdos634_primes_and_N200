-- Draft/CaseALemmaFWritten.lean — Lemma F in the written form: the target is
-- similar to the tile, or isosceles with base angle an acute angle of the (right) tile and apex
-- n − 2a_l. Corollary of `lemmaF_all`.
import Erdos634.Draft.CaseALemmaF

open scoped BigOperators

namespace Erdos634.LemmaF

open Erdos634.LemmaS Erdos634.LemmaKStar

theorem sum3W (g : Fin 3 → ℕ) {k l m : Fin 3} (h1 : k ≠ l) (h2 : k ≠ m) (h3 : l ≠ m) :
    ∑ i, g i = g k + g l + g m := by
  rw [Fin.sum_univ_three]
  fin_cases k <;> fin_cases l <;> fin_cases m <;> simp_all <;> omega

theorem thirdW (k l : Fin 3) (h : k ≠ l) : ∃ m, k ≠ m ∧ l ≠ m := by
  fin_cases k <;> fin_cases l <;>
    first
    | exact absurd rfl h
    | exact ⟨0, by decide, by decide⟩
    | exact ⟨1, by decide, by decide⟩
    | exact ⟨2, by decide, by decide⟩

theorem lemmaF_written {n : ℕ} {a : Fin 3 → ℕ} {f : Fin 3 → Fin 3 → ℕ}
    (hpos : ∀ i, 1 ≤ a i) (hsum : ∑ i, a i = n) (hf : ∀ j, f j ≠ 0)
    (hu : ∑ j, uu a f j = n) (he : ev f ∈ trivSpace n a) :
    LemmaF.Similar a f ∨
      ∃ k l : Fin 3, 2 * a k = n ∧ l ≠ k ∧ 2 * a l < n ∧
        ∃ j₁ j₂ j₃ : Fin 3, j₁ ≠ j₂ ∧ j₁ ≠ j₃ ∧ j₂ ≠ j₃ ∧
          uu a f j₁ = a l ∧ uu a f j₂ = a l ∧ uu a f j₃ + 2 * a l = n := by
  rcases lemmaF_all hpos hsum hf hu he with h | ⟨k, l, hk, hlk, j₁, j₂, hj, h₁, h₂⟩
  · exact Or.inl h
  · right
    obtain ⟨m, hkm, hlm⟩ := thirdW k l (Ne.symm hlk)
    have hs := sum3W a (Ne.symm hlk) hkm hlm
    have hm := hpos m
    obtain ⟨j₃, h13, h23⟩ := thirdW j₁ j₂ hj
    have hs' := sum3W (uu a f) hj h13 h23
    refine ⟨k, l, hk, hlk, by omega, j₁, j₂, j₃, hj, h13, h23, h₁, h₂, by omega⟩

end Erdos634.LemmaF

#print axioms Erdos634.LemmaF.lemmaF_written
