import Erdos634.Gamma2Alpha

namespace Erdos634.Draft.Gamma2AlphaWrap

/-- Thin wrapper: the γ=2α parametrization — integer-sided triangles with γ=2α and no common
factor are exactly the `(k², m²-k², km)` family with `Coprime k m`, `k < m`. -/
theorem wrap_gamma2alpha_param (a b c : ℕ) (hb : 0 < b)
    (hc : c ^ 2 = a ^ 2 + a * b) (hcop : Nat.gcd (Nat.gcd a b) c = 1) :
    ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ a = k ^ 2 ∧ b = m ^ 2 - k ^ 2 ∧ c = k * m :=
  gamma2alpha_param a b c hb hc hcop

-- Non-vacuity: (a,b,c) = (1,3,2) satisfies the hypotheses: 4 = 1 + 1·3, gcd=1.
example : ∃ k m : ℕ, Nat.Coprime k m ∧ k < m ∧ (1 : ℕ) = k ^ 2 ∧ 3 = m ^ 2 - k ^ 2 ∧ 2 = k * m :=
  wrap_gamma2alpha_param 1 3 2 (by norm_num) (by norm_num) (by norm_num)

#print axioms wrap_gamma2alpha_param

end Erdos634.Draft.Gamma2AlphaWrap
