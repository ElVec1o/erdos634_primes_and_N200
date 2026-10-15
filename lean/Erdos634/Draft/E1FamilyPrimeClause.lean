-- The prime corollary of the e = 1 family theorem:
-- for f ≥ 2, if 3f²−1 is prime, then 3f²−1 is not a tile count.
import Erdos634.Draft.PrimeCharacterization
import Mathlib.Tactic

namespace Erdos634.Draft.E1FamilyPrimeClause

open Erdos634.Geometry

/-- For f ≥ 2, if 3f²−1 is prime, then 3f²−1 is not a tile count.
    This is the prime clause of the e = 1 family theorem:
    no prime p = 3f²−1 (for f ≥ 2) is a tile count.
    Proof: 3f²−1 ≡ 3 (mod 4) when f is even (the only parity allowing 3f²−1 to be prime);
    odd f ≥ 3 forces 3f²−1 even and > 2, contradicting primality.
    Then `prime_tile_count_iff` closes: primes ≡ 3 (mod 4) greater than 3 are not tile counts. -/
theorem e1_prime_not_tile_count (f : ℕ) (hf : 2 ≤ f) (hp : (3 * f ^ 2 - 1).Prime) :
    ¬ Nonempty (CongruentDissection (3 * f ^ 2 - 1)) := by
  rw [Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff _ hp]
  push Not
  refine ⟨?_, ?_⟩
  · -- 3f²-1 ≠ 3: since f ≥ 2, 3f²-1 ≥ 11, but omega needs 3f² ≥ 12 first (ℕ subtraction)
    have hbig : 12 ≤ 3 * f ^ 2 := by nlinarith
    omega
  · -- (3f²-1) % 4 = 3: case split on parity of f
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Nat.even_or_odd f
    · -- f = k + k (even): 3f²-1 = 12k²-1 ≡ 3 (mod 4)
      have hfk : f = 2 * k := by omega
      have hk1 : 1 ≤ k := by omega
      rw [hfk]
      have heq : 3 * (2 * k) ^ 2 = 12 * k ^ 2 := by ring
      rw [heq]
      have h12 : 12 * k ^ 2 % 4 = 0 := by
        have h : 12 * k ^ 2 = 4 * (3 * k ^ 2) := by ring
        rw [h]; exact Nat.mul_mod_right 4 _
      have hge : 1 ≤ 12 * k ^ 2 := by nlinarith
      omega
    · -- f = 2k+1 (odd): 3f²-1 is even and ≥ 26, so not prime — contradiction
      exfalso
      have hfge3 : 3 ≤ f := by omega
      have hbig : 27 ≤ 3 * f ^ 2 := by nlinarith
      -- 3*(2k+1)²-1 = 2*(6k²+6k+1), so 2 ∣ 3f²-1
      have hdvd2 : 2 ∣ 3 * f ^ 2 - 1 := by
        rw [hk]
        exact ⟨6 * k ^ 2 + 6 * k + 1, by
          have h1 : 3 * (2 * k + 1) ^ 2 = 2 * (6 * k ^ 2 + 6 * k + 1) + 1 := by ring
          have h2 : 1 ≤ 3 * (2 * k + 1) ^ 2 := by nlinarith
          omega⟩
      -- 3f²-1 ≥ 26 > 2, so can't be prime and even
      have hgt2 : 2 < 3 * f ^ 2 - 1 := by omega
      rcases hp.eq_one_or_self_of_dvd 2 hdvd2 with h | h <;> omega

#print axioms e1_prime_not_tile_count

end Erdos634.Draft.E1FamilyPrimeClause
