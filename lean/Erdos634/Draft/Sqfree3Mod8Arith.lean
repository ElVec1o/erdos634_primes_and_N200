/-
Draft/Sqfree3Mod8Arith.lean -- the arithmetic leaves of the classification chain for `N ≡ 3 (mod 8)`.

Every leaf below is proved for all `N` in a residue class (some need `3 ∤ N` or `N` squarefree), by reduction
modulo 8 (finite checks in `ZMod 8`, `ZMod 4`) and parity descents.  They are assembled in `Sqfree3Mod8.lean`.

* `nsq_3mod8`, `harith_3mod8`, `exists_prime_ge7`: sums of two squares, the forms `c r²`, a prime `≥ 7` of odd
  valuation;
* `s2Arith_3mod8`: targets `(2α, α, 2β)`: `N X² = S² A B` forces `N ≡ 1, 5 (mod 8)` (`q` even) or contradicts the
  parity of the 2-adic valuation (`two_odd_sq`);
* `isoH9b_3mod8`: isosceles targets with a `2π/3` tile: `b` odd gives `N ≡ 1 (mod 8)`, `b` even is impossible;
* `noF2_3mod8`, `noF3z_3mod8`, `noF4z_3mod8`: the scalene `2π/3` targets;
* `e60_disc_not_sq`, `e120_pairs`, `f1Pair_3mod8`: the discriminants of the equilateral and `F₁` pairs are `≡ 20
  (mod 32)`, never squares; for squarefree `N` with `3 ∤ N` the side-word condition of the `2π/3` pairs fails.

Composite-N work; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.TwoPrime
import Erdos634.Draft.F1PairCert
import Erdos634.Draft.E60Irr
import Erdos634.Draft.CompositeE5Gen

open scoped Classical

namespace Erdos634.Draft.Sqfree3Mod8

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.AllNExclusion Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF Erdos634.Draft.R8Gen2
open Erdos634.Geometry.CaseA.LemmaH (HArith)
open Erdos634.Draft.F1PairCert (F1Pair f1Pair_of_arith)

variable {N : ℕ}

/-! ## Finite checks -/

theorem z8_odd_sq : ∀ x : ZMod 8, (2 * x + 1) ^ 2 = 1 := by decide
theorem z8_sq_ne3 : ∀ x : ZMod 8, x ^ 2 ≠ 3 := by decide
theorem z8_sq_ne5 : ∀ x : ZMod 8, x ^ 2 ≠ 5 := by decide
theorem z8_sq_ne6 : ∀ x : ZMod 8, x ^ 2 ≠ 2 * 3 := by decide
theorem z4_sq_ne3 : ∀ x : ZMod 4, x ^ 2 ≠ 3 := by decide
theorem z4_sumsq : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide
theorem z8_prod1 : ∀ x y : ZMod 8, x * y = 1 → x = y := by decide
theorem z8_prod3 : ∀ x y : ZMod 8, x * y = 3 → x + y = 4 := by decide
theorem z8_three_ne_one : (3 : ZMod 8) ≠ 1 := by decide

theorem z8_f2 : ∀ X R Z : ZMod 8, (3 : ZMod 8) = (X + R) * (2 * X + R) → (3 : ZMod 8) ≠ 3 * Z ^ 2 - X ^ 2 := by
  decide +kernel

theorem z8_f4 : ∀ X R Z : ZMod 8, (3 : ZMod 8) = (X + R) * (2 * X + R) → Z ^ 2 ≠ X ^ 2 + X * R + R ^ 2 := by
  decide +kernel

theorem z8_s3 : ∀ E Dd R : ZMod 8,
    (3 : ZMod 8) ≠ Dd * R ^ 2 * (2 * E + Dd) * (E ^ 2 + 4 * E * Dd + 2 * Dd ^ 2) := by
  decide +kernel

theorem z8_s2 : ∀ M Nn S : ZMod 8,
    (3 : ZMod 8) * ((M + M - (2 * Nn + 1)) * (2 * (M + M) + (2 * Nn + 1))) ^ 2
      ≠ S ^ 2 * (2 * (M + M) ^ 2 - (2 * Nn + 1) ^ 2) * (3 * (M + M) ^ 2 - (2 * Nn + 1) ^ 2) := by
  decide +kernel

theorem cast8 (h8 : N % 8 = 3) : ((N : ℕ) : ZMod 8) = 3 := by
  rw [← ZMod.natCast_mod, h8]
  rfl

theorem cast4 (h8 : N % 8 = 3) : ((N : ℕ) : ZMod 4) = 3 := by
  have h4 : N % 4 = 3 := by omega
  rw [← ZMod.natCast_mod, h4]
  rfl

theorem odd_int (h8 : N % 8 = 3) : Odd (N : ℤ) := ⟨((N / 2 : ℕ) : ℤ), by omega⟩

theorem odd_cast_sq {x : ℤ} (h : Odd x) : ((x : ℤ) : ZMod 8) ^ 2 = 1 := by
  obtain ⟨y, rfl⟩ := h
  push_cast
  exact z8_odd_sq _

/-! ## Sums of two squares, the forms `c r²`, a large prime -/

theorem nsq_3mod8 (h8 : N % 8 = 3) : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have h' := congrArg (Nat.cast : ℕ → ZMod 4) h
  push_cast at h'
  rw [cast4 h8] at h'
  exact z4_sumsq _ _ h'.symm

theorem harith_3mod8 (h8 : N % 8 = 3) (h3 : ¬ 3 ∣ N) : HArith N := by
  have hc := cast8 h8
  refine ⟨by omega, fun r h => ?_, fun t h => ?_, fun y h => ?_, fun t h => ?_, fun x h => ?_, fun r h => ?_⟩
  · omega
  · have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    rw [hc] at h'
    exact z8_sq_ne3 _ h'
  · omega
  · have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    rw [hc] at h'
    exact z8_sq_ne6 _ h'
  · omega
  · omega

theorem prime_ge7 {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h3 : q ≠ 3) (h5 : q ≠ 5) : 7 ≤ q := by
  have := hq.two_le
  by_contra hlt
  push Not at hlt
  have h4 : q ≠ 4 := fun h => by rw [h] at hq; exact absurd hq (by decide)
  have h6 : q ≠ 6 := fun h => by rw [h] at hq; exact absurd hq (by decide)
  omega

theorem exists_prime_ge7 (hsq : Squarefree N) (h8 : N % 8 = 3) (h3 : ¬ 3 ∣ N) :
    ∃ ℓ : ℕ, ℓ.Prime ∧ 7 ≤ ℓ ∧ ¬ Even (padicValNat ℓ N) := by
  have hN0 : N ≠ 0 := by omega
  obtain ⟨ℓ, hℓ, hℓN, hℓ7⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ ℓ ∣ N ∧ 7 ≤ ℓ := by
    by_cases h5 : 5 ∣ N
    · obtain ⟨M, hM⟩ := h5
      have hM1 : M ≠ 1 := by
        rintro rfl
        omega
      have hp := Nat.minFac_prime hM1
      have hdM := Nat.minFac_dvd M
      have hd : M.minFac ∣ N := hdM.trans ⟨5, by rw [hM]; ring⟩
      refine ⟨M.minFac, hp, hd, prime_ge7 hp ?_ ?_ ?_⟩
      · intro h
        rw [h] at hd
        omega
      · intro h
        rw [h] at hd
        exact h3 hd
      · intro h
        rw [h] at hdM
        have h55 : 5 * 5 ∣ N := by
          rw [hM]
          exact Nat.mul_dvd_mul_left 5 hdM
        exact absurd (Nat.isUnit_iff.mp (hsq 5 h55)) (by norm_num)
    · have hN1 : N ≠ 1 := by omega
      have hp := Nat.minFac_prime hN1
      have hd := Nat.minFac_dvd N
      refine ⟨N.minFac, hp, hd, prime_ge7 hp ?_ ?_ ?_⟩
      · intro h
        rw [h] at hd
        omega
      · intro h
        rw [h] at hd
        exact h3 hd
      · intro h
        rw [h] at hd
        exact h5 hd
  haveI := Fact.mk hℓ
  have hle : padicValNat ℓ N ≤ 1 := by
    rw [← Nat.factorization_def N hℓ]
    exact hsq.natFactorization_le_one ℓ
  have hge : 1 ≤ padicValNat ℓ N := one_le_padicValNat_of_dvd hN0 hℓN
  refine ⟨ℓ, hℓ, hℓ7, ?_⟩
  have h1 : padicValNat ℓ N = 1 := by omega
  rw [h1]
  decide

/-! ## A parity descent -/

/-- `2 M U² = O V²` with `M`, `O` odd and `U ≠ 0` is impossible. -/
theorem two_odd_sq : ∀ (n : ℕ) (M O U V : ℤ), U.natAbs = n → Odd M → Odd O → U ≠ 0 →
    2 * M * U ^ 2 = O * V ^ 2 → False := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M O U V hn hM hO hU h
    have hV : Even V := by
      have h1 : Even (O * V ^ 2) := ⟨M * U ^ 2, by rw [← h]; ring⟩
      rcases Int.even_mul.mp h1 with h2 | h2
      · exact absurd h2 (Int.not_even_iff_odd.mpr hO)
      · exact (Int.even_pow' two_ne_zero).mp h2
    obtain ⟨V₁, rfl⟩ := hV
    have h2 : M * U ^ 2 = 2 * (O * V₁ ^ 2) := by
      have h3 : 2 * (M * U ^ 2) = 2 * (2 * (O * V₁ ^ 2)) := by linear_combination h
      exact mul_left_cancel₀ two_ne_zero h3
    have hUe : Even U := by
      have h1 : Even (M * U ^ 2) := ⟨O * V₁ ^ 2, by rw [h2]; ring⟩
      rcases Int.even_mul.mp h1 with h3 | h3
      · exact absurd h3 (Int.not_even_iff_odd.mpr hM)
      · exact (Int.even_pow' two_ne_zero).mp h3
    obtain ⟨U₁, rfl⟩ := hUe
    have hU1 : U₁ ≠ 0 := by
      rintro rfl
      exact hU (by norm_num)
    have h3 : 2 * M * U₁ ^ 2 = O * V₁ ^ 2 := by
      have h4 : 2 * (2 * M * U₁ ^ 2) = 2 * (O * V₁ ^ 2) := by linear_combination h2
      exact mul_left_cancel₀ two_ne_zero h4
    have hlt : U₁.natAbs < n := by
      rw [← hn]
      have h5 : (U₁ + U₁).natAbs = 2 * U₁.natAbs := by
        rw [← two_mul, Int.natAbs_mul]
        rfl
      have h6 : 0 < U₁.natAbs := Int.natAbs_pos.mpr hU1
      omega
    exact ih U₁.natAbs hlt M O U₁ V₁ rfl hM hO hU1 h3

/-! ## The targets `(2α, α, 2β)` -/

theorem s2Arith_3mod8 (h8 : N % 8 = 3) : S2Arith N := by
  intro p q S hp hpq hcop _ heq
  have hc := cast8 h8
  have hNodd := odd_int h8
  rcases Int.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩ <;> rcases Int.even_or_odd p with ⟨n, hn⟩ | ⟨n, hn⟩
  · -- both even: not coprime
    obtain ⟨u, v, huv⟩ := hcop
    have h2 : (2 : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left ⟨n, by rw [hn]; ring⟩ _) (Dvd.dvd.mul_left ⟨m, by rw [hm]; ring⟩ _)
    norm_num at h2
  · -- `q` even, `p` odd: residues modulo 8
    have h' := congrArg (Int.cast : ℤ → ZMod 8) heq
    push_cast at h'
    have hq8 : ((q : ℤ) : ZMod 8) = (m : ZMod 8) + m := by
      rw [hm]
      push_cast
      ring
    have hp8 : ((p : ℤ) : ZMod 8) = 2 * (n : ZMod 8) + 1 := by
      rw [hn]
      push_cast
      ring
    rw [hc, hq8, hp8] at h'
    exact z8_s2 (m : ZMod 8) (n : ZMod 8) (S : ZMod 8) (by linear_combination h')
  · -- `q` odd, `p` even
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

/-! ## Isosceles targets with a `2π/3` tile -/

theorem isoH9b_3mod8 (h8 : N % 8 = 3) : IsoH9b N := by
  intro a b c k nA ha hb hc hk hcc h3 hcop hdvd hne hbN hkc hpar
  have hc8 := cast8 h8
  have hNodd := odd_int h8
  obtain ⟨n₁, hn₁⟩ := hdvd
  have he0 : a + 2 * b ≠ 0 := by linarith
  have hk2 : b * n₁ = k ^ 2 := by
    have h1 : (a + 2 * b) * (b * n₁) = (a + 2 * b) * k ^ 2 := by
      rw [hn₁] at hbN
      linear_combination hbN
    exact mul_left_cancel₀ he0 h1
  obtain ⟨hOe, hOn⟩ : Odd (a + 2 * b) ∧ Odd n₁ := by
    rw [hn₁] at hNodd
    exact Int.odd_mul.mp hNodd
  have hOa : Odd a := by
    have h1 : a = (a + 2 * b) - 2 * b := by ring
    rw [h1]
    exact Odd.sub_even hOe ⟨b, by ring⟩
  have hOnA : Odd nA := by
    obtain ⟨j, hj⟩ := hpar
    have h1 : nA = (N : ℤ) + 2 * j := by linarith
    rw [h1]
    exact hNodd.add_even ⟨j, by ring⟩
  rcases Int.even_or_odd b with hEb | hOb
  · -- `b` even
    obtain ⟨t, ht⟩ : ∃ t : ℤ, t = c - a - b := ⟨_, rfl⟩
    have hkt : k * t = nA * b := by rw [ht]; exact hkc
    have hnt : n₁ * t = nA * k := by
      have h1 : b * (n₁ * t) = b * (nA * k) := by linear_combination t * hk2 + k * hkt
      exact mul_left_cancel₀ hb.ne' h1
    have hquad : t ^ 2 + 2 * (a + b) * t + a * b = 0 := by
      rw [ht]
      linear_combination hcc
    have hn0 : n₁ ≠ 0 := by
      rintro rfl
      simp at hOn
    have hE : nA ^ 2 * b + 2 * (a + b) * nA * k + n₁ * a * b = 0 := by
      have h1 : n₁ * (nA ^ 2 * b + 2 * (a + b) * nA * k + n₁ * a * b) = n₁ * 0 := by
        linear_combination n₁ ^ 2 * hquad - (n₁ * t + nA * k + 2 * (a + b) * n₁) * hnt + nA ^ 2 * hk2
      exact mul_left_cancel₀ hn0 h1
    obtain ⟨W₁, hW⟩ : Even (nA ^ 2 + n₁ * a) := Odd.add_odd hOnA.pow (hOn.mul hOa)
    have hsq : b * (b * (nA ^ 2 + n₁ * a) ^ 2) = b * (4 * (a + b) ^ 2 * nA ^ 2 * n₁) := by
      linear_combination (b * (nA ^ 2 + n₁ * a) - 2 * (a + b) * nA * k) * hE
        - 4 * (a + b) ^ 2 * nA ^ 2 * hk2
    have hsq' := mul_left_cancel₀ hb.ne' hsq
    rw [hW] at hsq'
    have h4 : b * W₁ ^ 2 = (a + b) ^ 2 * nA ^ 2 * n₁ := by
      have h5 : 4 * (b * W₁ ^ 2) = 4 * ((a + b) ^ 2 * nA ^ 2 * n₁) := by linear_combination hsq'
      exact mul_left_cancel₀ (by norm_num) h5
    have hev : Even (b * W₁ ^ 2) := hEb.mul_right _
    have hod : Odd ((a + b) ^ 2 * nA ^ 2 * n₁) := (((hOa.add_even hEb).pow).mul hOnA.pow).mul hOn
    rw [h4] at hev
    exact (Int.not_even_iff_odd.mpr hod) hev
  · -- `b` odd: `N ≡ 1 (mod 8)`
    have hOk : Odd k := by
      have h1 : Odd (k ^ 2) := by
        rw [← hk2]
        exact hOb.mul hOn
      exact (Int.odd_pow' two_ne_zero).mp h1
    have hOc : Odd c := by
      have h1 : Odd (c ^ 2) := by
        rw [hcc]
        exact ((hOa.pow).add_odd (hOa.mul hOb)).add_odd hOb.pow
      exact (Int.odd_pow' two_ne_zero).mp h1
    have hA2 := odd_cast_sq hOa
    have hB2 := odd_cast_sq hOb
    have hC2 := odd_cast_sq hOc
    have hK2 := odd_cast_sq hOk
    have hcc8 := congrArg (Int.cast : ℤ → ZMod 8) hcc
    push_cast at hcc8
    have hk8 := congrArg (Int.cast : ℤ → ZMod 8) hk2
    push_cast at hk8
    have hn8 := congrArg (Int.cast : ℤ → ZMod 8) hn₁
    push_cast at hn8
    rw [hc8] at hn8
    have e3 : (a : ZMod 8) * b = -1 := by linear_combination (-1 : ZMod 8) * hcc8 - hA2 - hB2 + hC2
    have e2 : (b : ZMod 8) * n₁ = 1 := hk8.trans hK2
    have h31 : (3 : ZMod 8) = 1 := by
      linear_combination hn8 + ((b : ZMod 8) * n₁) * e3 + e2 - ((a : ZMod 8) * n₁) * hB2
    exact z8_three_ne_one h31

/-! ## The scalene `2π/3` targets -/

theorem noF2_3mod8 (h8 : N % 8 = 3) (h3 : ¬ 3 ∣ N) : NoF2 N := by
  have hc := cast8 h8
  refine noF2_of_int N ?_ ?_
  · intro z hz
    have h1 : (3 : ℤ) ∣ (N : ℤ) := ⟨z ^ 2, hz⟩
    exact h3 (by exact_mod_cast h1)
  · intro x r _ _ hN z hz
    have h1 := congrArg (Nat.cast : ℕ → ZMod 8) hN
    push_cast at h1
    rw [hc] at h1
    have h2 := congrArg (Int.cast : ℤ → ZMod 8) hz
    push_cast at h2
    rw [hc] at h2
    exact z8_f2 (x : ZMod 8) (r : ZMod 8) (z : ZMod 8) (by linear_combination h1) (by linear_combination h2)

theorem noF4z_3mod8 (h8 : N % 8 = 3) : NoF4z N := by
  have hc := cast8 h8
  refine noF4z_of_int N ?_
  intro x r _ _ hN z hz
  have h1 := congrArg (Nat.cast : ℕ → ZMod 8) hN
  push_cast at h1
  rw [hc] at h1
  have h2 := congrArg (Int.cast : ℤ → ZMod 8) hz
  push_cast at h2
  exact z8_f4 (x : ZMod 8) (r : ZMod 8) (z : ZMod 8) (by linear_combination h1) (by linear_combination h2)

theorem noF3z_3mod8 (h3 : ¬ 3 ∣ N) : NoF3z N := by
  intro s j z _ _ _ heq _
  have h1 : (3 : ℤ) ∣ ((4 * N : ℕ) : ℤ) := ⟨(s + j) * (s + 3 * j), by push_cast; linarith⟩
  have h2 : 3 ∣ 4 * N := by exact_mod_cast h1
  omega

/-! ## Equilateral pairs and `F₁` pairs -/

/-- odd factors of `3N`, `N ≡ 3 (mod 8)`, are congruent modulo 8 -/
theorem factors_congr (h8 : N % 8 = 3) (s t : ℤ) (hprod : s * t = 3 * (N : ℤ)) : (8 : ℤ) ∣ s - t := by
  have hc := cast8 h8
  have hp8 := congrArg (Int.cast : ℤ → ZMod 8) hprod
  push_cast at hp8
  rw [hc] at hp8
  have h9 : (3 : ZMod 8) * 3 = 1 := by decide
  rw [h9] at hp8
  have heq8 := z8_prod1 _ _ hp8
  have h0 : ((s - t : ℤ) : ZMod 8) = 0 := by
    push_cast
    rw [heq8, sub_self]
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (s - t) 8).mp h0
  exact_mod_cast h1

/-- the discriminant of a `π/3` pair on the equilateral triangle is not a square -/
theorem e60_disc_not_sq (h8 : N % 8 = 3) (m₁ m₂ : ℤ) (h2 : (2 : ℤ) ∣ m₂ - N)
    (hprod : m₁ * m₂ = 3 * (N : ℤ)) : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) := by
  have hc := cast8 h8
  have hNodd := odd_int h8
  obtain ⟨u, hu⟩ := factors_congr h8 m₁ m₂ hprod
  have hO2 : Odd m₂ := by
    obtain ⟨j, hj⟩ := h2
    have h1 : m₂ = (N : ℤ) + 2 * j := by linarith
    rw [h1]
    exact hNodd.add_even ⟨j, by ring⟩
  rintro ⟨r, hr⟩
  have hOw : Odd (m₂ + 4 * u) := hO2.add_even ⟨2 * u, by ring⟩
  have hsum : m₁ + m₂ = 2 * (m₂ + 4 * u) := by linarith
  rw [hsum] at hr
  have hre : Even r := by
    have h1 : Even (r * r) := ⟨2 * (m₂ + 4 * u) ^ 2 - 8 * (N : ℤ), by rw [← hr]; ring⟩
    rcases Int.even_mul.mp h1 with h | h <;> exact h
  obtain ⟨r₁, rfl⟩ := hre
  have hr1 : r₁ ^ 2 = (m₂ + 4 * u) ^ 2 - 4 * (N : ℤ) := by
    have h1 : 4 * r₁ ^ 2 = 4 * ((m₂ + 4 * u) ^ 2 - 4 * (N : ℤ)) := by linear_combination (-1 : ℤ) * hr
    exact mul_left_cancel₀ (by norm_num) h1
  have h8' := congrArg (Int.cast : ℤ → ZMod 8) hr1
  push_cast at h8'
  have hw2 := odd_cast_sq hOw
  push_cast at hw2
  rw [hw2, hc] at h8'
  exact z8_sq_ne5 _ (h8'.trans (by decide))

/-- the pairs of the `2π/3` tiles on the equilateral triangle -/
theorem e120_pairs (hsq : Squarefree N) (h8 : N % 8 = 3) (h3 : ¬ 3 ∣ N) :
    ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * (N : ℤ) ≠ r * (s + t) := by
  intro s t hs1 _ ht1 _ hprod
  constructor
  · obtain ⟨u, hu⟩ := factors_congr h8 t s (by rw [mul_comm]; exact hprod)
    rintro ⟨r, hr⟩
    rw [hu] at hr
    have hre : Even r := by
      have h1 : Even (r * r) := ⟨32 * u ^ 2 + 8 * (N : ℤ), by rw [← hr]; ring⟩
      rcases Int.even_mul.mp h1 with h | h <;> exact h
    obtain ⟨r₁, rfl⟩ := hre
    have h2 : r₁ ^ 2 = 4 * (4 * u ^ 2 + (N : ℤ)) := by
      have h1 : 4 * r₁ ^ 2 = 4 * (4 * (4 * u ^ 2 + (N : ℤ))) := by linear_combination (-1 : ℤ) * hr
      exact mul_left_cancel₀ (by norm_num) h1
    have hre1 : Even r₁ := by
      have h1 : Even (r₁ ^ 2) := ⟨2 * (4 * u ^ 2 + (N : ℤ)), by rw [h2]; ring⟩
      exact (Int.even_pow' two_ne_zero).mp h1
    obtain ⟨r₂, rfl⟩ := hre1
    have h3' : r₂ ^ 2 = 4 * u ^ 2 + (N : ℤ) := by
      have h1 : 4 * r₂ ^ 2 = 4 * (4 * u ^ 2 + (N : ℤ)) := by linear_combination h2
      exact mul_left_cancel₀ (by norm_num) h1
    have h4 := congrArg (Int.cast : ℤ → ZMod 4) h3'
    push_cast at h4
    have h40 : (4 : ZMod 4) = 0 := by decide
    rw [h40, zero_mul, zero_add, cast4 h8] at h4
    exact z4_sq_ne3 _ h4
  · intro r hr0 h2N
    obtain ⟨s', rfl⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ s)
    obtain ⟨t', rfl⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ t)
    obtain ⟨r', rfl⟩ := Int.eq_ofNat_of_zero_le hr0
    have hst : s' * t' = 3 * N := by exact_mod_cast hprod
    have h2 : 2 * N = r' * (s' + t') := by exact_mod_cast h2N
    have hs1' : 1 ≤ s' := by exact_mod_cast hs1
    have ht1' : 1 ≤ t' := by exact_mod_cast ht1
    have h3N : Squarefree (3 * N) := Nat.squarefree_mul_iff.mpr
      ⟨(Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3, Nat.prime_three.prime.squarefree, hsq⟩
    have hcop : Nat.Coprime s' t' := by
      rw [← hst] at h3N
      exact (Nat.squarefree_mul_iff.mp h3N).1
    have key : 2 * (s' * t') = 3 * r' * (s' + t') := by
      rw [hst]
      linarith [h2]
    have hs_dvd : s' ∣ 3 * r' * t' := by
      have h1 : s' ∣ 3 * r' * s' + 3 * r' * t' := ⟨2 * t', by linarith [key]⟩
      exact (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp h1
    have hs3 : s' ∣ 3 * r' := hcop.dvd_of_dvd_mul_right hs_dvd
    have ht_dvd : t' ∣ 3 * r' * s' := by
      have h1 : t' ∣ 3 * r' * t' + 3 * r' * s' := ⟨2 * s', by linarith [key]⟩
      exact (Nat.dvd_add_right (Dvd.intro_left _ rfl)).mp h1
    have ht3 : t' ∣ 3 * r' := hcop.symm.dvd_of_dvd_mul_right ht_dvd
    have hst3 : s' * t' ∣ 3 * r' := hcop.mul_dvd_of_dvd_of_dvd hs3 ht3
    rw [hst] at hst3
    have hNr : N ∣ r' := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hst3
    have hN0 : 0 < N := by omega
    have hr0' : 0 < r' := by
      rcases Nat.eq_zero_or_pos r' with h | h
      · rw [h] at h2
        omega
      · exact h
    have hle : N ≤ r' := Nat.le_of_dvd hr0' hNr
    have hsum : s' + t' ≤ 2 := by
      by_contra hgt
      push Not at hgt
      have h5 : N * 3 ≤ r' * (s' + t') := Nat.mul_le_mul hle hgt
      omega
    have hs'1 : s' = 1 := by omega
    have ht'1 : t' = 1 := by omega
    rw [hs'1, ht'1] at hst
    omega

/-- every `F₁` pair has a non-square discriminant -/
theorem f1Pair_3mod8 (h8 : N % 8 = 3) : ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N → F1Pair N Ma Mb := by
  intro Ma Mb h1 hlt hprod
  have hc := cast8 h8
  have hp8 : (Ma : ZMod 8) * (Mb : ZMod 8) = 3 := by
    have h' := congrArg (Nat.cast : ℕ → ZMod 8) hprod
    push_cast at h'
    rw [hc] at h'
    exact h'
  obtain ⟨hOa, hOb⟩ : Odd Ma ∧ Odd Mb := by
    have h2 : Odd (Ma * Mb) := by
      rw [hprod]
      exact ⟨N / 2, by omega⟩
    exact Nat.odd_mul.mp h2
  obtain ⟨i, hi⟩ := hOa
  obtain ⟨j, hj⟩ := hOb
  have hA2 : (Ma : ZMod 8) ^ 2 = 1 := by
    rw [hi]
    push_cast
    exact z8_odd_sq _
  have hB2 : (Mb : ZMod 8) ^ 2 = 1 := by
    rw [hj]
    push_cast
    exact z8_odd_sq _
  -- `Ma + Mb = 4 (2w + 1)`
  have hsum8 : (Ma + Mb) % 8 = 4 := by
    have h2 := z8_prod3 _ _ hp8
    have h3 : (((Ma + Mb : ℕ)) : ZMod 8) = ((4 : ℕ) : ZMod 8) := by
      push_cast
      exact h2
    have h4 := (ZMod.natCast_eq_natCast_iff' (Ma + Mb) 4 8).mp h3
    omega
  obtain ⟨w, hw⟩ : ∃ w : ℕ, Ma + Mb = 4 * (2 * w + 1) := ⟨(Ma + Mb) / 8, by omega⟩
  refine f1Pair_of_arith N Ma Mb (j - i) (by omega) (by omega) hprod (by omega) ?_ ?_
  · rintro ⟨r, hr⟩
    have hsum : (Ma : ℤ) + Mb = 4 * (2 * (w : ℤ) + 1) := by exact_mod_cast hw
    rw [hsum] at hr
    have hre : Even r := by
      have h2 : Even (r * r) := ⟨8 * (2 * (w : ℤ) + 1) ^ 2 + 6 * (N : ℤ), by rw [← hr]; ring⟩
      rcases Int.even_mul.mp h2 with h | h <;> exact h
    obtain ⟨r₁, rfl⟩ := hre
    have hr1 : r₁ ^ 2 = 4 * (2 * (w : ℤ) + 1) ^ 2 + 3 * (N : ℤ) := by
      have h2 : 4 * r₁ ^ 2 = 4 * (4 * (2 * (w : ℤ) + 1) ^ 2 + 3 * (N : ℤ)) := by
        linear_combination (-1 : ℤ) * hr
      exact mul_left_cancel₀ (by norm_num) h2
    have h8' := congrArg (Int.cast : ℤ → ZMod 8) hr1
    push_cast at h8'
    rw [z8_odd_sq, hc] at h8'
    exact z8_sq_ne5 _ (h8'.trans (by decide))
  · intro h
    have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    have h2 : (1 : ZMod 8) + 1 = 4 * 3 := by linear_combination h' - hA2 - hB2 + 4 * hp8
    exact absurd h2 (by decide)

end Erdos634.Draft.Sqfree3Mod8

#print axioms Erdos634.Draft.Sqfree3Mod8.s2Arith_3mod8
#print axioms Erdos634.Draft.Sqfree3Mod8.isoH9b_3mod8
#print axioms Erdos634.Draft.Sqfree3Mod8.e120_pairs
#print axioms Erdos634.Draft.Sqfree3Mod8.f1Pair_3mod8
