/-
Draft/QPExact.lean -- the equation of the target `(2α, α, 2β)` for odd squarefree `N`, and the sector `5 (mod 8)` in
its explicit form.

`qp_exact`: if `N` is odd and squarefree and `N ((q − p)(2q + p))² = S² (2q² − p²)(3q² − p²)` with coprime
`0 < p < q`, `S ≠ 0`, then `N = (2q² − p²)(3q² − p²)`.  (For `q` odd the equation has no solution, by the 2-adic
descent `Sqfree3Mod8.two_odd_sq`; for `q` even and `p` odd the number `X = (q − p)(2q + p)` is coprime to
`(2q² − p²)(3q² − p²)`, so `X ∣ S`, and the cofactor is a unit because `N` is squarefree.)

`tile_sqfree_5mod8_explicit`: a squarefree tile count `N ≡ 5 (mod 8)` prime to `3` is

    x² + y²,     or     (2q² − p²)(3q² − p²)  (coprime 0 < p < q),     or     d (2e + d)(e² + 4ed + 2d²).

`sector5_below_517`: below `517` the only such tile count that is not a sum of two squares is `77`.

Composite-N theorem.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.Sqfree5Mod8

open scoped Classical

namespace Erdos634.Draft.QPExact

open Erdos634.Geometry Erdos634.Draft.TileCountFamilies
open Erdos634.Draft.Sqfree3Mod8 (two_odd_sq)

variable {N : ℕ}

/-- **The equation of the target `(2α, α, 2β)` for odd squarefree `N`.** -/
theorem qp_exact (hsq : Squarefree N) (hNodd : Odd (N : ℤ)) (p q S : ℤ) (hp : 0 < p) (hpq : p < q)
    (hcop : IsCoprime p q) (hS : S ≠ 0)
    (heq : (N : ℤ) * ((q - p) * (2 * q + p)) ^ 2 = S ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) :
    (N : ℤ) = (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) := by
  rcases Int.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩ <;> rcases Int.even_or_odd p with ⟨n, hn⟩ | ⟨n, hn⟩
  · -- both even: not coprime
    exfalso
    obtain ⟨u, v, huv⟩ := hcop
    have h2 : (2 : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left ⟨n, by rw [hn]; ring⟩ _) (Dvd.dvd.mul_left ⟨m, by rw [hm]; ring⟩ _)
    norm_num at h2
  · -- `q` even, `p` odd: `X` is coprime to `A B`
    have hX2 : IsCoprime (q - p) 2 := ⟨-1, m - n, by rw [hm, hn]; ring⟩
    have hY2 : IsCoprime (2 * q + p) 2 := ⟨1, -(2 * m + n), by rw [hm, hn]; ring⟩
    have hXp : IsCoprime (q - p) p := by
      have e : q - p = q + (-1) * p := by ring
      rw [e]
      exact hcop.symm.add_mul_right_left (-1)
    have hYq : IsCoprime (2 * q + p) q := by
      have e : 2 * q + p = p + 2 * q := by ring
      rw [e]
      exact hcop.add_mul_right_left 2
    have hXA : IsCoprime (q - p) (2 * q ^ 2 - p ^ 2) := by
      have e : 2 * q ^ 2 - p ^ 2 = p ^ 2 + (q - p) * (2 * (q + p)) := by ring
      rw [e]
      exact (hXp.pow_right).add_mul_left_right _
    have hXB : IsCoprime (q - p) (3 * q ^ 2 - p ^ 2) := by
      have e : 3 * q ^ 2 - p ^ 2 = 2 * p ^ 2 + (q - p) * (3 * (q + p)) := by ring
      rw [e]
      exact (hX2.mul_right hXp.pow_right).add_mul_left_right _
    have hYA : IsCoprime (2 * q + p) (2 * q ^ 2 - p ^ 2) := by
      have e : 2 * q ^ 2 - p ^ 2 = -(2 * q ^ 2) + (2 * q + p) * (2 * q - p) := by ring
      rw [e]
      exact ((hY2.mul_right hYq.pow_right).neg_right).add_mul_left_right _
    have hYB : IsCoprime (2 * q + p) (3 * q ^ 2 - p ^ 2) := by
      have e : 3 * q ^ 2 - p ^ 2 = -(q ^ 2) + (2 * q + p) * (2 * q - p) := by ring
      rw [e]
      exact ((hYq.pow_right).neg_right).add_mul_left_right _
    have hXAB : IsCoprime ((q - p) * (2 * q + p)) ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) :=
      (hXA.mul_right hXB).mul_left (hYA.mul_right hYB)
    have hX2AB : IsCoprime (((q - p) * (2 * q + p)) ^ 2) ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) :=
      hXAB.pow_left
    have hdvd : ((q - p) * (2 * q + p)) ^ 2 ∣ S ^ 2 * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) :=
      ⟨(N : ℤ), by linear_combination (-1 : ℤ) * heq⟩
    have hdvd2 : ((q - p) * (2 * q + p)) ^ 2 ∣ S ^ 2 := hX2AB.dvd_of_dvd_mul_right hdvd
    have hdvd1 : (q - p) * (2 * q + p) ∣ S := (Int.pow_dvd_pow_iff two_ne_zero).mp hdvd2
    obtain ⟨S₁, hS₁⟩ := hdvd1
    have hXne : (q - p) * (2 * q + p) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    have hX2ne : ((q - p) * (2 * q + p)) ^ 2 ≠ 0 := pow_ne_zero 2 hXne
    have hN : (N : ℤ) = S₁ * S₁ * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) := by
      have h1 : ((q - p) * (2 * q + p)) ^ 2 * (N : ℤ)
          = ((q - p) * (2 * q + p)) ^ 2 * (S₁ * S₁ * ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2))) := by
        rw [hS₁] at heq
        linear_combination heq
      exact mul_left_cancel₀ hX2ne h1
    have hsqZ : Squarefree (N : ℤ) := Int.squarefree_natCast.mpr hsq
    have hunit : IsUnit S₁ := hsqZ S₁ ⟨(2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2), hN⟩
    have hS1 : S₁ * S₁ = 1 := by
      rcases Int.isUnit_iff.mp hunit with h | h <;> rw [h] <;> norm_num
    rw [hN, hS1, one_mul]
  · -- `q` odd, `p` even
    exfalso
    subst hm hn
    refine two_odd_sq _ (N : ℤ) (((2 * m + 1) ^ 2 - 2 * n ^ 2) * (3 * (2 * m + 1) ^ 2 - 4 * n ^ 2))
      ((2 * m + 1 - 2 * n) * (2 * m + 1 + n)) S rfl hNodd ?_ ?_ ?_
    · exact Odd.mul ⟨2 * m ^ 2 + 2 * m - n ^ 2, by ring⟩ ⟨6 * m ^ 2 + 6 * m + 1 - 2 * n ^ 2, by ring⟩
    · exact mul_ne_zero (by omega) (by omega)
    · have h4 : 2 * (2 * (N : ℤ) * ((2 * m + 1 - 2 * n) * (2 * m + 1 + n)) ^ 2)
          = 2 * (((2 * m + 1) ^ 2 - 2 * n ^ 2) * (3 * (2 * m + 1) ^ 2 - 4 * n ^ 2) * S ^ 2) := by
        linear_combination heq
      exact mul_left_cancel₀ two_ne_zero h4
  · -- both odd
    exfalso
    subst hm hn
    refine two_odd_sq _ (N : ℤ)
      ((2 * (2 * m + 1) ^ 2 - (2 * n + 1) ^ 2) * (6 * m ^ 2 + 6 * m + 1 - 2 * n ^ 2 - 2 * n))
      ((m - n) * (4 * m + 2 * n + 3)) S rfl hNodd ?_ ?_ ?_
    · exact Odd.mul ⟨4 * m ^ 2 + 4 * m - 2 * n ^ 2 - 2 * n, by ring⟩ ⟨3 * m ^ 2 + 3 * m - n ^ 2 - n, by ring⟩
    · exact mul_ne_zero (by omega) (by omega)
    · have h4 : 2 * (2 * (N : ℤ) * ((m - n) * (4 * m + 2 * n + 3)) ^ 2)
          = 2 * ((2 * (2 * m + 1) ^ 2 - (2 * n + 1) ^ 2) * (6 * m ^ 2 + 6 * m + 1 - 2 * n ^ 2 - 2 * n)
            * S ^ 2) := by
        linear_combination heq
      exact mul_left_cancel₀ two_ne_zero h4

/-- **The sector `N ≡ 5 (mod 8)`, explicit form.**  If a triangle is cut into `N` congruent triangles, with `N`
squarefree, `N ≡ 5 (mod 8)` and `3 ∤ N`, then `N = x² + y²`, or `N = (2q² − p²)(3q² − p²)` for coprime
`0 < p < q`, or `N = d (2e + d)(e² + 4ed + 2d²)` with `gcd(e, e + d) = 1` (that is `(f² − e²)(2f² − e²)`,
`f = e + d`). -/
theorem tile_sqfree_5mod8_explicit (hsq : Squarefree N) (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N)
    (D : CongruentDissection N) :
    (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ∨
    (∃ p q : ℤ, 0 < p ∧ p < q ∧ IsCoprime p q ∧ (N : ℤ) = (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) ∨
    (∃ e d : ℕ, 1 ≤ e ∧ 1 ≤ d ∧ Nat.Coprime e (e + d) ∧
      N = d * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
  rcases Erdos634.Draft.Sqfree5Mod8.tile_sqfree_5mod8_form hsq h8 h3 D with h | ⟨p, q, S, hp, hpq, hcop, hS, heq⟩ | h
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨p, q, hp, hpq, hcop,
      qp_exact hsq (Erdos634.Draft.Sqfree5Mod8.odd_int h8) p q S hp hpq hcop hS heq⟩)
  · exact Or.inr (Or.inr h)

/-- form (ii) is realized whenever `q² > 2p²` (the layout `L(p, q)`, `S2G.s2_family_gen`) -/
theorem form_ii_realized (p q : ℕ) (hp : 1 ≤ p) (hg : 2 * p ^ 2 < q ^ 2) :
    TileCount ((2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) :=
  Erdos634.Draft.S2G.s2_family_gen p q hp hg

/-- **Below `517`**: a squarefree `N ≡ 5 (mod 8)` prime to `3` that is not a sum of two squares is a tile count
only for `N = 77`.  (`517 = 11 · 47` is the base-`α` count of the member `(5, 6)`; it is not covered by this statement.) -/
theorem sector5_below_517 (hsq : Squarefree N) (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N)
    (h2 : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2) (hlt : N < 517) : TileCount N ↔ N = 77 := by
  constructor
  · rintro ⟨D⟩
    rcases tile_sqfree_5mod8_explicit hsq h8 h3 D with h | ⟨p, q, hp, hpq, -, hN⟩ | ⟨e, d, he, hd, -, hN⟩
    · exact absurd h h2
    · have hNlt : (N : ℤ) < 517 := by exact_mod_cast hlt
      have hq : q ≤ 3 := by
        by_contra hc
        have hq4 : 4 ≤ q := by omega
        have hp2 : p ^ 2 ≤ (q - 1) ^ 2 := by nlinarith
        have hA : 23 ≤ 2 * q ^ 2 - p ^ 2 := by nlinarith
        have hB : 39 ≤ 3 * q ^ 2 - p ^ 2 := by nlinarith
        have h1 : (23 : ℤ) * 39 ≤ (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2) :=
          mul_le_mul hA hB (by norm_num) (by linarith)
        linarith
      have hq2 : 2 ≤ q := by omega
      interval_cases q <;> interval_cases p <;> norm_num at hN <;> omega
    · have hd3 : d ≤ 3 := by
        by_contra hc
        have hd4 : 4 ≤ d := by omega
        have h1 : 6 ≤ 2 * e + d := by omega
        have h2' : 49 ≤ e ^ 2 + 4 * e * d + 2 * d ^ 2 := by
          nlinarith [Nat.mul_le_mul he hd4, Nat.mul_le_mul hd4 hd4, Nat.mul_le_mul he he]
        have hprod : 4 * 6 * 49 ≤ d * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul hd4 h1) h2'
        rw [← hN] at hprod
        omega
      have he4 : e ≤ 4 := by
        by_contra hc
        have he5 : 5 ≤ e := by omega
        have h1 : 11 ≤ 2 * e + d := by omega
        have h2' : 47 ≤ e ^ 2 + 4 * e * d + 2 * d ^ 2 := by
          nlinarith [Nat.mul_le_mul he5 hd, Nat.mul_le_mul hd hd, Nat.mul_le_mul he5 he5]
        have hprod : 1 * 11 * 47 ≤ d * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul hd h1) h2'
        rw [← hN] at hprod
        omega
      interval_cases e <;> interval_cases d <;> norm_num at hN <;> omega
  · rintro rfl
    exact Erdos634.Draft.Sqfree5Mod8.sector5_sharp_77.2.2.2.1

end Erdos634.Draft.QPExact

#print axioms Erdos634.Draft.QPExact.qp_exact
#print axioms Erdos634.Draft.QPExact.tile_sqfree_5mod8_explicit
#print axioms Erdos634.Draft.QPExact.sector5_below_517
