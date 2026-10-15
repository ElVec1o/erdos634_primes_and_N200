-- Draft/FDDSpectrumPaper.lean — the spectrum theorem as one statement with its three clauses.
-- The paper defines the *invariant conditions* of a target as integrality and parity of the two
-- boundary invariants `M_α`, `M_β` (`cor:int`: `M ∈ ℤ`, `M ≡ N (mod 2)`) together with the area
-- equation, and states that the counts `N` satisfying all of them are exactly Zhang's family.
-- Admissibility is necessary, not sufficient: the theorem is the arithmetic characterisation of the
-- admissible set, not a realizability claim.
-- The three Lean iff-theorems below are stated with the paper's own `M_α = k(2b+a−2c)/(c+a−b)`,
-- `M_β = k(2b+a+2c)/(c+b−a)` (base-α; mirror for base-β; `3ak/X − k`, `3ak/Y + k` for `F₁`),
-- area equations `N b = k²(a+2b)` / `N a = k²(2a+b)` / `N b = k²(a+b)`.
import Erdos634.Draft.FDDSpectrumArith

namespace Erdos634.Draft.FDDSpectrumPaper

open Erdos634.Draft.FDDSpectrum

/-- **`thm:spectrum`** (paper statement, all three clauses).  Let `(a,b,c)` be a primitive
`120°`-triple (`a,b > 0`, `gcd(a,b) = 1`, `c² = a²+ab+b²`).  The tile counts `N` for which some scale
`k ≥ 1` satisfies the area equation and makes both invariants `M_α`, `M_β` integers `≡ N (mod 2)` are,
on the base-`α` isosceles target, exactly `N = m² b(a+2b)`; on the base-`β` target exactly
`N = m² a(2a+b)`; on the `F₁` target exactly `N = m² b(a+b)` (`m ≥ 1`). -/
theorem spectrum_paper (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (N : ℕ) :
    ((∃ k : ℕ, 0 < k ∧ N * b = k ^ 2 * (a + 2 * b) ∧
      ∃ Ma Mb : ℤ, Ma * ((c : ℤ) + a - b) = k * (2 * b + a - 2 * c) ∧
        Mb * ((c : ℤ) + b - a) = k * (2 * b + a + 2 * c) ∧
        (2 : ℤ) ∣ Ma - N ∧ (2 : ℤ) ∣ Mb - N)
      ↔ ∃ m : ℕ, 0 < m ∧ N = m ^ 2 * b * (a + 2 * b)) ∧
    ((∃ k : ℕ, 0 < k ∧ N * a = k ^ 2 * (b + 2 * a) ∧
      ∃ Ma Mb : ℤ, Ma * ((c : ℤ) + b - a) = k * (2 * a + b - 2 * c) ∧
        Mb * ((c : ℤ) + a - b) = k * (2 * a + b + 2 * c) ∧
        (2 : ℤ) ∣ Ma - N ∧ (2 : ℤ) ∣ Mb - N)
      ↔ ∃ m : ℕ, 0 < m ∧ N = m ^ 2 * a * (2 * a + b)) ∧
    ((∃ k : ℕ, 0 < k ∧ N * b = k ^ 2 * (a + b) ∧
      ∃ Ma Mb : ℤ, Ma * ((c : ℤ) + a - b) = k * (2 * a + b - c) ∧
        Mb * ((c : ℤ) + b - a) = k * (2 * a + b + c) ∧
        (2 : ℤ) ∣ Ma - N ∧ (2 : ℤ) ∣ Mb - N)
      ↔ ∃ m : ℕ, 0 < m ∧ N = m ^ 2 * b * (a + b)) :=
  ⟨spectrum_alpha_iff a b c N ha hb hcop hc, spectrum_beta_iff a b c N ha hb hcop hc,
   spectrum_F1_iff a b c N ha hb hcop hc⟩

end Erdos634.Draft.FDDSpectrumPaper

#print axioms Erdos634.Draft.FDDSpectrumPaper.spectrum_paper
