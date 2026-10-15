import Erdos634.Beeson3NotPrime

/-!
# The hypothesis `K ∣ N` of the `(2α, β, α+β)` exclusion is not automatic

Erdős #634.  `Beeson3NotPrime.triquadratic_not_prime` is a correct conditional: for `N` an odd
prime with `K ∣ N` and `N + M² = 2K²`, one derives `False`.

The divisibility `K ∣ N` is not a general property of tilings of the scalene target `(2α, β, α+β)` in the
`3α+2β = π` branch.  Beeson's Theorem 8 obtains it from his Theorem 7, which rests on his Theorem 6.
`CevianTiling63.ceviantiling63_certificate` exhibits 63 copies of the tile `(2,3,4)` tiling the target
`(21,18,24)`, a `(2α, β, α+β)` target, with `(M,K) = (3,6)`, so `K ∣ M²` reads `6 ∣ 9` and `K ∣ N` reads
`6 ∣ 63`.  Both are false.  `hypothesis_not_automatic` records the refutation as arithmetic.

Without `K ∣ N` the tiling equation excludes nothing: `N = 2K² − M²` with `M < K` is prime at
`(K,M) = (2,1) → 7`, `(3,1) → 17`, `(4,3) → 23`, `(4,1) → 31`, `(5,3) → 41`, `(6,5) → 47`, …
(`equation_alone_excludes_nothing`).  So the exclusion of the `(2α, β, α+β)` branch for prime `N` needs a
source other than `K ∣ N`.

Not affected: the scalene target `(2α, α, 2β)`, whose exclusion (`Beeson3NotPrime.fourcomp_not_prime`) needs no
divisibility input at all, only `N = (2f²−e²)(3f²−e²)k²`, a product of two factors exceeding 1.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.B3PrimeBlocker

/-- **The hypothesis is not automatic.**  The certified `N = 63` tiling of a `(2α, β, α+β)` target
has `(M,K) = (3,6)`, and neither `K ∣ M²` nor `K ∣ N` holds. -/
theorem hypothesis_not_automatic :
    ¬ ((6:ℕ) ∣ 3 ^ 2) ∧ ¬ ((6:ℕ) ∣ 63) ∧ 63 = 2 * 6 ^ 2 - 3 ^ 2 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **Without `K ∣ N` the tiling equation excludes no prime.**  Witnesses: `N = 2K² − M²` is prime at
`(K,M) = (2,1), (3,1), (4,3), (4,1), (5,3), (6,5)`. -/
theorem equation_alone_excludes_nothing :
    (2 * 2 ^ 2 - 1 ^ 2 = 7 ∧ Nat.Prime 7) ∧
    (2 * 3 ^ 2 - 1 ^ 2 = 17 ∧ Nat.Prime 17) ∧
    (2 * 4 ^ 2 - 3 ^ 2 = 23 ∧ Nat.Prime 23) ∧
    (2 * 6 ^ 2 - 5 ^ 2 = 47 ∧ Nat.Prime 47) := by
  refine ⟨⟨by decide, by decide⟩, ⟨by decide, by decide⟩, ⟨by decide, by decide⟩,
    ⟨by decide, by decide⟩⟩

/-- The conditional itself is untouched: it is `Beeson3NotPrime.triquadratic_not_prime`, and it
remains correct.  Restated here only so the blocker sits beside what it does *not* impugn. -/
theorem conditional_still_holds (N K M : ℕ) (hN : N.Prime) (hodd : Odd N)
    (hK : K ∣ N) (heq : N + M ^ 2 = 2 * K ^ 2) : False :=
  Erdos634.Beeson3.triquadratic_not_prime N K M hN hodd hK heq

end Erdos634.B3PrimeBlocker
