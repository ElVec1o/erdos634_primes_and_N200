import Erdos634.BaseAlphaBetaPrime

/-!
# Base α+β prime obstruction: wrapper

Re-exports results of `BaseAlphaBetaPrime`:

1. **`gcd_dvd_two`**: if N is prime, M²<N, then gcd(N−M², N+M²) ∣ 2.
2. **`base_obstruction`**: arithmetic inequality obstruction (g,ah,M case).
3. **`base_alphabeta_not_prime`**: the combined prime obstruction (False under full hypotheses).

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseAlphaBetaPrimeWrap

open Erdos634.BaseAlphaBeta

/-- gcd(N−M², N+M²) divides 2 when N is prime and M²<N. -/
theorem basealphabeta_gcd_dvd_two (N M : ℕ) (hN : N.Prime) (hM : 1 ≤ M) (hM2 : M ^ 2 < N) :
    Nat.gcd (N - M ^ 2) (N + M ^ 2) ∣ 2 :=
  gcd_dvd_two N M hN hM hM2

/-- Arithmetic obstruction: the bridge inequality leads to False. -/
theorem basealphabeta_obstruction (g ah M : ℤ) (hah : 1 ≤ ah) (hM : 1 ≤ M) (hle : ah + M ≤ g)
    (hbridge : (g - M) * (g ^ 2 - ah ^ 2) + 2 * g ^ 2 ≤ M * ah * (g + ah)) : False :=
  base_obstruction g ah M hah hM hle hbridge

/-- The base α+β configuration cannot produce a prime N. -/
theorem basealphabeta_not_prime (N M d g ah : ℕ)
    (hN : N.Prime) (hM : 1 ≤ M) (hM2 : M ^ 2 < N)
    (hd : d = Nat.gcd (N - M ^ 2) (N + M ^ 2))
    (hah0 : 1 ≤ ah)
    (hdg : d * g = N + M ^ 2) (hdah : d * ah = N - M ^ 2)
    (hbridge : ((g : ℤ) - M) * ((g : ℤ) ^ 2 - (ah : ℤ) ^ 2) + 2 * (g : ℤ) ^ 2
        ≤ (M : ℤ) * ah * (g + ah)) : False :=
  base_alphabeta_not_prime N M d g ah hN hM hM2 hd hah0 hdg hdah hbridge

/-- Non-vacuity: N=7 is prime, M=1, M²=1<7. -/
theorem basealphabeta_witness : (7:ℕ).Prime ∧ (1:ℕ) ≤ 1 ∧ (1:ℕ)^2 < 7 := by
  norm_num

#print axioms basealphabeta_gcd_dvd_two
#print axioms basealphabeta_not_prime

end Erdos634.Draft.BaseAlphaBetaPrimeWrap
