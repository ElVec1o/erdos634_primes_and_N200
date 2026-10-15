import Erdos634.FCStep2

/-!
# FCStep2 — four-component prime forces N=2: wrapper

Key results:
- `chain_unconditional`: the main theorem — from N·R² = M²·A·B with A=2f²-e², B=3f²-e²,
  gcd(e,f)=1, N prime, M≠0, forces N=2.
- `split_of_raw`: steps (2)+(3) composed — from N·R² = M²·A·B, forces A·B = (Nu²,v²) or (u²,Nv²)
- `sq_dvd_prime_eq_one`: a² ∣ N prime implies a = 1

No sorry, standard axioms.
-/

namespace Erdos634.Draft.FCStep2Wrap

open Erdos634.FCStep2

/-- THE main result: raw tiling equation N·R² = M²·(2f²-e²)·(3f²-e²) with N prime, gcd(e,f)=1,
0 < e < f, M ≠ 0 forces N = 2. -/
theorem fc2_chain_unconditional {e f M R : ℤ} {N : ℕ}
    (hc : IsCoprime e f) (hN : N.Prime) (he : 0 < e) (hef : e < f) (hM : M ≠ 0)
    (h : (N : ℤ) * R ^ 2 = M ^ 2 * (2 * f ^ 2 - e ^ 2) * (3 * f ^ 2 - e ^ 2)) : N = 2 :=
  chain_unconditional hc hN he hef hM h

/-- Steps (2)+(3): raw equation + N prime + gcd(A,B)=1 forces split of A·B. -/
theorem fc2_split_of_raw {A B M R : ℤ} {N : ℕ} (hN : N.Prime) (hAB : IsCoprime A B)
    (hA : 0 < A) (hB : 0 < B) (hM : M ≠ 0) (h : (N : ℤ) * R ^ 2 = M ^ 2 * A * B) :
    (∃ u v : ℤ, A = (N : ℤ) * u ^ 2 ∧ B = v ^ 2) ∨
    (∃ u v : ℤ, A = u ^ 2 ∧ B = (N : ℤ) * v ^ 2) :=
  split_of_raw hN hAB hA hB hM h

/-- a² ∣ N prime implies a = 1 (no nontrivial square divisor). -/
theorem fc2_sq_dvd_prime_eq_one {a N : ℕ} (hN : N.Prime) (h : a ^ 2 ∣ N) : a = 1 :=
  sq_dvd_prime_eq_one hN h

-- Non-vacuity: sq_dvd_prime_eq_one at a=1, N=5
example : fc2_sq_dvd_prime_eq_one (a := 1) (N := 5) (by norm_num) (by norm_num) = rfl := rfl

-- Non-vacuity: split_of_raw at N=3, A=3, B=4
example : (∃ u v : ℤ, (3 : ℤ) = ((3 : ℕ) : ℤ) * u ^ 2 ∧ (4 : ℤ) = v ^ 2) ∨
    (∃ u v : ℤ, (3 : ℤ) = u ^ 2 ∧ (4 : ℤ) = ((3 : ℕ) : ℤ) * v ^ 2) :=
  fc2_split_of_raw (M := 1) (R := 2) (by norm_num) ⟨-1, 1, by norm_num⟩
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

#print axioms fc2_chain_unconditional
#print axioms fc2_split_of_raw

end Erdos634.Draft.FCStep2Wrap
