/-
Draft/Sqfree7Mod8.lean -- **the sector `N ≡ 7 (mod 8)`: squarefree, `3 ∤ N`.**

`tile_sqfree_7mod8_form`: if a triangle is cut into `N` congruent triangles, `N` squarefree, `N % 8 = 7`, `3 ∤ N`,
then there are positive integers `a, b, c` with `c² = a² + ab + b²` and

    N = a b      or      N = (a + 2b)(2a + b).

So in this residue class (natural density `3/(4π²)`, the same as the class `N ≡ 3 (mod 8)` of `Sqfree3Mod8`) every
branch of the classification is closed except two rows of the tiles with an angle `2π/3`, each at scale one:
the equilateral target (`N = ab`) and the target `F₂` with angles `(2α, 2β, α + β)` (`N = (a+2b)(2a+b)`).  The
values of the two forms up to `X` number `O(√X)`.  The class is NOT empty of tile counts: `143 = (3+10)(6+5)` is one
(`N143.tileCount_143`), so the statement cannot be improved to an exclusion (`sector_sharp_143`).  Below `455` it is
the only one: `sector_below_455 : TileCount N ↔ N = 143` for the `N < 455` of the class.

Proof: the squarefree chain `ChainIso.chain_gen3_iso`, every leaf for the whole class, as in `Sqfree3Mod8`:
* commensurable angles, similar tile, right tile, `γ = 2α`: `N` squarefree, `N ≡ 3 (mod 4)`;
* `3α + 2β = π`: base-`β` at scale one (`basebeta_full_unc`); `(2α, α, 2β)`: `N ≡ 1, 5 (mod 8)` or a 2-adic
  parity contradiction (`s2Arith_7mod8`); base-`α`: the count is `≡ 1, 5 (mod 8)` (`s3Closed_7mod8`);
* `2π/3` tiles: isosceles targets need `N ≡ 1 (mod 8)` (`isoH9b_7mod8`); `F₄` needs `N ≡ 1 (mod 8)`
  (`noF4z_7mod8`); `F₃` needs `3 ∣ N`; `F₁` and the `π/3` tiles on the equilateral triangle: every pair has a
  discriminant `≡ 20 (mod 32)` (`f1Pair_7mod8`, `e60_disc_not_sq`);
* the `2π/3` tiles on the equilateral triangle: a pair with a square discriminant gives `N = ab` with
  `a² + ab + b²` a square (`e120_pairs`), the other pairs die by the side-word condition (coprimality);
* `F₂`: `N = (x + r)(2x + r)` with `N + x² = 3z²` gives `3 ∣ r`, and `a = r/3`, `b = x + r/3` (`noF2_of_form`).

What is NOT proved: that the two exceptional forms are tile counts (true for `143`; open for `455 = 13 · 35`, the
equilateral triangle of side `455` and the tile `(13, 35, 43)`).  The theorem stands or falls with
`basebeta_full_unc`, like `Sqfree3Mod8`.

Composite-N theorem.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.Sqfree3Mod8
import Erdos634.Draft.N143
import Erdos634.Draft.Sqfree7Mod8Chk

open scoped Classical

namespace Erdos634.Draft.Sqfree7Mod8

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.AllNExclusion Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF Erdos634.Draft.R8Gen2
open Erdos634.Draft.TileCountFamilies
open Erdos634.Geometry.CaseA.LemmaH (HArith)
open Erdos634.Draft.F1PairCert (F1Pair f1Pair_of_arith)
open Erdos634.Draft.Sqfree3Mod8 (z8_odd_sq z8_sq_ne5 z4_sumsq two_odd_sq prime_ge7 odd_cast_sq noF3z_3mod8
  s3inst_of_not_dvd)
open Erdos634.Draft.Sqfree7Mod8Chk (chk_ab chk_f2)

variable {N : ℕ}

/-! ## Finite checks -/

theorem z8_sq_ne7 : ∀ x : ZMod 8, x ^ 2 ≠ 7 := by decide
theorem z8_sq_ne14 : ∀ x : ZMod 8, x ^ 2 ≠ 2 * 7 := by decide
theorem z8_prod5 : ∀ x y : ZMod 8, x * y = 5 → x = 5 * y := by decide
theorem z8_prod7 : ∀ x y : ZMod 8, x * y = 7 → x + y = 0 := by decide
theorem z8_seven_ne_one : (7 : ZMod 8) ≠ 1 := by decide
theorem z8_f1 : ∀ x w : ZMod 8, x ^ 2 ≠ 16 * w ^ 2 + 3 * 7 := by decide

theorem z8_f4 : ∀ X R Z : ZMod 8, (7 : ZMod 8) = (X + R) * (2 * X + R) → Z ^ 2 ≠ X ^ 2 + X * R + R ^ 2 := by
  decide +kernel

theorem z8_s3 : ∀ E Dd R : ZMod 8,
    (7 : ZMod 8) ≠ Dd * R ^ 2 * (2 * E + Dd) * (E ^ 2 + 4 * E * Dd + 2 * Dd ^ 2) := by
  decide +kernel

theorem z8_s2 : ∀ M Nn S : ZMod 8,
    (7 : ZMod 8) * ((M + M - (2 * Nn + 1)) * (2 * (M + M) + (2 * Nn + 1))) ^ 2
      ≠ S ^ 2 * (2 * (M + M) ^ 2 - (2 * Nn + 1) ^ 2) * (3 * (M + M) ^ 2 - (2 * Nn + 1) ^ 2) := by
  decide +kernel

theorem cast8 (h8 : N % 8 = 7) : ((N : ℕ) : ZMod 8) = 7 := by
  rw [← ZMod.natCast_mod, h8]
  rfl

theorem cast4 (h8 : N % 8 = 7) : ((N : ℕ) : ZMod 4) = 3 := by
  have h4 : N % 4 = 3 := by omega
  rw [← ZMod.natCast_mod, h4]
  rfl

theorem odd_int (h8 : N % 8 = 7) : Odd (N : ℤ) := ⟨((N / 2 : ℕ) : ℤ), by omega⟩

/-! ## Sums of two squares, the forms `c r²`, a large prime -/

theorem nsq_7mod8 (h8 : N % 8 = 7) : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have h' := congrArg (Nat.cast : ℕ → ZMod 4) h
  push_cast at h'
  rw [cast4 h8] at h'
  exact z4_sumsq _ _ h'.symm

theorem harith_7mod8 (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N) : HArith N := by
  have hc := cast8 h8
  refine ⟨by omega, fun r h => ?_, fun t h => ?_, fun y h => ?_, fun t h => ?_, fun x h => ?_, fun r h => ?_⟩
  · omega
  · have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    rw [hc] at h'
    exact z8_sq_ne7 _ h'
  · omega
  · have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    rw [hc] at h'
    exact z8_sq_ne14 _ h'
  · omega
  · omega

theorem exists_prime_ge7 (hsq : Squarefree N) (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N) :
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

/-! ## The targets `(2α, α, 2β)` -/

theorem s2Arith_7mod8 (h8 : N % 8 = 7) : S2Arith N := by
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

theorem isoH9b_7mod8 (h8 : N % 8 = 7) : IsoH9b N := by
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
    have h71 : (7 : ZMod 8) = 1 := by
      linear_combination hn8 + ((b : ZMod 8) * n₁) * e3 + e2 - ((a : ZMod 8) * n₁) * hB2
    exact z8_seven_ne_one h71

/-! ## The scalene `2π/3` targets -/

theorem noF4z_7mod8 (h8 : N % 8 = 7) : NoF4z N := by
  have hc := cast8 h8
  refine noF4z_of_int N ?_
  intro x r _ _ hN z hz
  have h1 := congrArg (Nat.cast : ℕ → ZMod 8) hN
  push_cast at h1
  rw [hc] at h1
  have h2 := congrArg (Int.cast : ℤ → ZMod 8) hz
  push_cast at h2
  exact z8_f4 (x : ZMod 8) (r : ZMod 8) (z : ZMod 8) (by linear_combination h1) (by linear_combination h2)

/-- **The `F₂` leaf from the form**: `N = (x + r)(2x + r)`, `N + x² = 3z²` gives `r = 3a` and the triple
`(a, x + a, |z|)` with `N = (a + 2b)(2a + b)`. -/
theorem noF2_of_form (h3 : ¬ 3 ∣ N)
    (hF2 : ∀ a b c : ℕ, 0 < a → 0 < b → c ^ 2 = a ^ 2 + a * b + b ^ 2 → N ≠ (a + 2 * b) * (2 * a + b)) :
    NoF2 N := by
  refine noF2_of_int N ?_ ?_
  · intro z hz
    have h1 : (3 : ℤ) ∣ (N : ℤ) := ⟨z ^ 2, hz⟩
    exact h3 (by exact_mod_cast h1)
  · intro x r hx hr hN z hz
    have hNi : (N : ℤ) = ((x : ℤ) + r) * (2 * x + r) := by exact_mod_cast hN
    have hr2 : (r : ℤ) ^ 2 = 3 * (z ^ 2 - (x : ℤ) ^ 2 - x * r) := by linear_combination hz - hNi
    have h3r : (3 : ℤ) ∣ (r : ℤ) := Int.prime_three.dvd_of_dvd_pow ⟨_, hr2⟩
    have h3r' : 3 ∣ r := by exact_mod_cast h3r
    obtain ⟨a, ha⟩ := h3r'
    subst ha
    have ha0 : 0 < a := by omega
    have hz2 : z ^ 2 = (x : ℤ) ^ 2 + 3 * x * a + 3 * (a : ℤ) ^ 2 := by
      push_cast at hr2
      have h9 : 3 * z ^ 2 = 3 * ((x : ℤ) ^ 2 + 3 * x * a + 3 * (a : ℤ) ^ 2) := by
        linear_combination (-1 : ℤ) * hr2
      exact mul_left_cancel₀ (by norm_num) h9
    have hcz : (z.natAbs : ℤ) ^ 2 = (a : ℤ) ^ 2 + a * ((x : ℤ) + a) + ((x : ℤ) + a) ^ 2 := by
      rw [Int.natAbs_pow_two, hz2]
      ring
    have hcN : z.natAbs ^ 2 = a ^ 2 + a * (x + a) + (x + a) ^ 2 := by
      refine Int.natCast_inj.mp ?_
      rw [Nat.cast_pow, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_mul, Nat.cast_pow, Nat.cast_add]
      exact hcz
    exact hF2 a (x + a) z.natAbs ha0 (by omega) hcN (by rw [hN]; ring)

/-! ## Equilateral pairs and `F₁` pairs -/

/-- odd factors of `3N`, `N ≡ 7 (mod 8)`: `s ≡ 5t (mod 8)` -/
theorem factors_congr5 (h8 : N % 8 = 7) (s t : ℤ) (hprod : s * t = 3 * (N : ℤ)) : (8 : ℤ) ∣ s - 5 * t := by
  have hc := cast8 h8
  have hp8 := congrArg (Int.cast : ℤ → ZMod 8) hprod
  push_cast at hp8
  rw [hc] at hp8
  have h21 : (3 : ZMod 8) * 7 = 5 := by decide
  rw [h21] at hp8
  have heq8 := z8_prod5 _ _ hp8
  have h0 : ((s - 5 * t : ℤ) : ZMod 8) = 0 := by
    push_cast
    rw [heq8, sub_self]
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (s - 5 * t) 8).mp h0
  exact_mod_cast h1

/-- the discriminant of a `π/3` pair on the equilateral triangle is not a square -/
theorem e60_disc_not_sq (h8 : N % 8 = 7) (m₁ m₂ : ℤ) (h2 : (2 : ℤ) ∣ m₂ - N)
    (hprod : m₁ * m₂ = 3 * (N : ℤ)) : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) := by
  have hc := cast8 h8
  have hNodd := odd_int h8
  obtain ⟨u, hu⟩ := factors_congr5 h8 m₁ m₂ hprod
  have hO2 : Odd m₂ := by
    obtain ⟨j, hj⟩ := h2
    have h1 : m₂ = (N : ℤ) + 2 * j := by linarith
    rw [h1]
    exact hNodd.add_even ⟨j, by ring⟩
  rintro ⟨r, hr⟩
  have h3odd : Odd (3 : ℤ) := ⟨1, by norm_num⟩
  have hO3 : Odd (3 * m₂) := h3odd.mul hO2
  have hOw : Odd (3 * m₂ + 4 * u) := hO3.add_even ⟨2 * u, by ring⟩
  have hsum : m₁ + m₂ = 2 * (3 * m₂ + 4 * u) := by linarith
  rw [hsum] at hr
  have hre : Even r := by
    have h1 : Even (r * r) := ⟨2 * (3 * m₂ + 4 * u) ^ 2 - 8 * (N : ℤ), by rw [← hr]; ring⟩
    rcases Int.even_mul.mp h1 with h | h <;> exact h
  obtain ⟨r₁, rfl⟩ := hre
  have hr1 : r₁ ^ 2 = (3 * m₂ + 4 * u) ^ 2 - 4 * (N : ℤ) := by
    have h1 : 4 * r₁ ^ 2 = 4 * ((3 * m₂ + 4 * u) ^ 2 - 4 * (N : ℤ)) := by linear_combination (-1 : ℤ) * hr
    exact mul_left_cancel₀ (by norm_num) h1
  have h8' := congrArg (Int.cast : ℤ → ZMod 8) hr1
  push_cast at h8'
  have hw2 := odd_cast_sq hOw
  push_cast at hw2
  rw [hw2, hc] at h8'
  exact z8_sq_ne5 _ (h8'.trans (by decide))

/-- the pairs of the `2π/3` tiles on the equilateral triangle: a square discriminant gives `N = ab` with
`a² + ab + b²` a square; the other pairs fail the side-word condition -/
theorem e120_pairs (hsq : Squarefree N) (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N)
    (hE : ∀ a b c : ℤ, a * b = (N : ℤ) → c ^ 2 ≠ a ^ 2 + a * b + b ^ 2) :
    ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * (N : ℤ) ≠ r * (s + t) := by
  intro s t hs1 _ ht1 _ hprod
  constructor
  · rintro ⟨r, hr⟩
    have hNodd := odd_int h8
    have h3odd : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have hOst : Odd (s * t) := by
      rw [hprod]
      exact h3odd.mul hNodd
    obtain ⟨hOs, hOt⟩ := Int.odd_mul.mp hOst
    obtain ⟨d, hd⟩ : Even (t - s) := Odd.sub_odd hOt hOs
    obtain ⟨c, hc⟩ : Even (s + t) := Odd.add_odd hOs hOt
    have hre : Even r := by
      have h1 : Even (r * r) := ⟨2 * d ^ 2 + 8 * (N : ℤ), by rw [← hr, hd]; ring⟩
      rcases Int.even_mul.mp h1 with h | h <;> exact h
    obtain ⟨e, rfl⟩ := hre
    have he : e ^ 2 = d ^ 2 + 4 * (N : ℤ) := by
      have h1 : 4 * e ^ 2 = 4 * (d ^ 2 + 4 * (N : ℤ)) := by
        rw [hd] at hr
        linear_combination (-1 : ℤ) * hr
      exact mul_left_cancel₀ (by norm_num) h1
    have hed : Even (e - d) := by
      by_contra hodd
      have ho : Odd (e - d) := Int.not_even_iff_odd.mp hodd
      have ho2 : Odd (e + d) := by
        have h1 : e + d = (e - d) + 2 * d := by ring
        rw [h1]
        exact ho.add_even ⟨d, by ring⟩
      have hpr : Odd ((e - d) * (e + d)) := ho.mul ho2
      have h4N : (e - d) * (e + d) = 4 * (N : ℤ) := by linear_combination he
      rw [h4N] at hpr
      exact (Int.not_even_iff_odd.mpr hpr) ⟨2 * (N : ℤ), by ring⟩
    obtain ⟨b, hb⟩ := hed
    have he' : e = b + b + d := by linarith
    have hab : (b + d) * b = (N : ℤ) := by
      have h4 : 4 * ((b + d) * b) = 4 * (N : ℤ) := by
        rw [he'] at he
        linear_combination he
      exact mul_left_cancel₀ (by norm_num) h4
    have hs : s = c - d := by linarith
    have ht : t = c + d := by linarith
    rw [hs, ht] at hprod
    exact hE (b + d) b c hab (by linear_combination hprod - 3 * hab)
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
theorem f1Pair_7mod8 (h8 : N % 8 = 7) : ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N → F1Pair N Ma Mb := by
  intro Ma Mb h1 hlt hprod
  have hc := cast8 h8
  have hp8 : (Ma : ZMod 8) * (Mb : ZMod 8) = 7 := by
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
  -- `Ma + Mb = 8 w`
  have hsum8 : (Ma + Mb) % 8 = 0 := by
    have h2 := z8_prod7 _ _ hp8
    have h3 : (((Ma + Mb : ℕ)) : ZMod 8) = ((0 : ℕ) : ZMod 8) := by
      push_cast
      exact h2
    have h4 := (ZMod.natCast_eq_natCast_iff' (Ma + Mb) 0 8).mp h3
    omega
  obtain ⟨w, hw⟩ : ∃ w : ℕ, Ma + Mb = 8 * w := ⟨(Ma + Mb) / 8, by omega⟩
  refine f1Pair_of_arith N Ma Mb (j - i) (by omega) (by omega) hprod (by omega) ?_ ?_
  · rintro ⟨r, hr⟩
    have hsum : (Ma : ℤ) + Mb = 8 * (w : ℤ) := by exact_mod_cast hw
    rw [hsum] at hr
    have hre : Even r := by
      have h2 : Even (r * r) := ⟨32 * (w : ℤ) ^ 2 + 6 * (N : ℤ), by rw [← hr]; ring⟩
      rcases Int.even_mul.mp h2 with h | h <;> exact h
    obtain ⟨r₁, rfl⟩ := hre
    have hr1 : r₁ ^ 2 = 16 * (w : ℤ) ^ 2 + 3 * (N : ℤ) := by
      have h2 : 4 * r₁ ^ 2 = 4 * (16 * (w : ℤ) ^ 2 + 3 * (N : ℤ)) := by
        linear_combination (-1 : ℤ) * hr
      exact mul_left_cancel₀ (by norm_num) h2
    have h8' := congrArg (Int.cast : ℤ → ZMod 8) hr1
    push_cast at h8'
    rw [hc] at h8'
    exact z8_f1 _ _ h8'
  · intro h
    have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    have h2 : (1 : ZMod 8) + 1 = 4 * 7 := by linear_combination h' - hA2 - hB2 + 4 * hp8
    exact absurd h2 (by decide)

/-! ## The leaves of the chain -/

/-- the base-`α` leaf for `N ≡ 7 (mod 8)` -/
theorem s3Closed_7mod8 (h8 : N % 8 = 7) : S3Closed N := by
  have hc := cast8 h8
  refine s3Closed_of_inst N ?_
  intro e d m he hd hcop heq
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h] at heq
      have hNd : N * d = 0 := by rw [heq]; ring
      have hN0 : 0 < N := by omega
      have := Nat.mul_pos hN0 hd
      omega
    · exact h
  rcases Classical.em (d ∣ m) with hdm | hdm
  · exfalso
    obtain ⟨r, rfl⟩ := hdm
    have h' : N = d * r ^ 2 * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2) := by
      have h1 : d * N = d * (d * r ^ 2 * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
        rw [mul_comm d N, heq]
        ring
      exact Nat.eq_of_mul_eq_mul_left hd h1
    have h8' := congrArg (Nat.cast : ℕ → ZMod 8) h'
    push_cast at h8'
    rw [hc] at h8'
    exact z8_s3 (e : ZMod 8) (d : ZMod 8) (r : ZMod 8) (by linear_combination h8')
  · have hnd : ¬ (e + d - e) ∣ m := by rwa [Nat.add_sub_cancel_left]
    intro N' D' a0 a1 a2 a3
    exact s3inst_of_not_dvd m e (e + d) he (by omega) hcop hm hnd D' a0 a1 a2 a3

theorem gapE60_7mod8 (h8 : N % 8 = 7) : GapE60 N := by
  intro D α a b c hα h hE
  obtain ⟨m₁, m₂, -, hp2, -, -, -, -, hS1, hS2, -, hprod, -, -⟩ := Row5.theoremE_sixty D hα h hE
  exact Erdos634.Draft.E60Irr.e60Pair_of_not_isSquare N m₁ m₂ (e60_disc_not_sq h8 m₁ m₂ hp2 hprod) D α a b c
    hα h hE hS1 hS2

theorem gapE120_7mod8 (hsq : Squarefree N) (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N)
    (hE : ∀ a b c : ℤ, a * b = (N : ℤ) → c ^ 2 ≠ a ^ 2 + a * b + b ^ 2) : GapE120 N :=
  Erdos634.Draft.CompositeE5Gen.gapE120_of_pairs N (by omega) (e120_pairs hsq h8 h3 hE)

theorem gapF1_7mod8 (h8 : N % 8 = 7) (h7 : 6 < N) : GapF1 N :=
  Erdos634.Draft.CompositeF1Gen.gapF1_of_MaGt1 N h7
    (Erdos634.Draft.F1PairCert.f1MaGt1_of_pairs N (f1Pair_7mod8 h8))

/-- the equilateral exception, from natural numbers to integers -/
theorem hE_int (hN0 : 0 < N)
    (hEq : ∀ a b c : ℕ, 0 < a → 0 < b → c ^ 2 = a ^ 2 + a * b + b ^ 2 → N ≠ a * b) :
    ∀ a b c : ℤ, a * b = (N : ℤ) → c ^ 2 ≠ a ^ 2 + a * b + b ^ 2 := by
  intro a b c hab hc
  have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hab
    linarith
  have hb0 : b ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    linarith
  have hmulN : a.natAbs * b.natAbs = N := by
    rw [← Int.natAbs_mul, hab, Int.natAbs_natCast]
  refine hEq a.natAbs b.natAbs c.natAbs (Int.natAbs_pos.mpr ha0) (Int.natAbs_pos.mpr hb0) ?_ hmulN.symm
  rw [hmulN]
  refine Int.natCast_inj.mp ?_
  rw [Nat.cast_pow, Nat.cast_add, Nat.cast_add, Nat.cast_pow, Nat.cast_pow, Int.natAbs_pow_two,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  linarith [hc, hab]

/-! ## The theorem -/

/-- **Squarefree `N ≡ 7 (mod 8)`, `3 ∤ N`, without the two exceptional forms: not a tile count.** -/
theorem not_tile_sqfree_7mod8 (hsq : Squarefree N) (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N)
    (hEq : ∀ a b c : ℕ, 0 < a → 0 < b → c ^ 2 = a ^ 2 + a * b + b ^ 2 → N ≠ a * b)
    (hF2 : ∀ a b c : ℕ, 0 < a → 0 < b → c ^ 2 = a ^ 2 + a * b + b ^ 2 → N ≠ (a + 2 * b) * (2 * a + b))
    (D : CongruentDissection N) : False := by
  by_cases h7 : N = 7
  · subst h7
    have h := (Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff 7 (by norm_num)).mp ⟨D⟩
    omega
  have h23 : 23 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hns := nsq_7mod8 h8
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := exists_prime_ge7 hsq h8 h3
  exact chain_gen3_iso N hsq (s1Closed_of_sqfree N hsq hN0)
    (s2Closed_of_arith N (s2Arith_7mod8 h8))
    (s3Closed_7mod8 h8)
    (fun D α a b c hα hd hi =>
      Erdos634.Draft.ThmIsoH9b.thmIso_H9b N D (isoH9b_7mod8 h8) α a b c hα hd hi)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq (by omega) (Or.inl (by omega)) hns
      (harith_7mod8 h8 h3) hℓ hℓ7 hodd)
    (caseB_of_sumsq N
      (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq (by omega) (Or.inl (by omega))) hns)
    (caseR_of_odd N (by omega))
    (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree N hsq)
    (gapE60_7mod8 h8) (gapE120_7mod8 hsq h8 h3 (hE_int hN0 hEq)) (gapF1_7mod8 h8 (by omega))
    (gapR8_of_arith_z N (noF2_of_form h3 hF2) (noF3z_3mod8 h3) (noF4z_7mod8 h8)) D

/-- **The sector `N ≡ 7 (mod 8)`.**  If a triangle is cut into `N` congruent triangles, with `N` squarefree,
`N ≡ 7 (mod 8)` and `3 ∤ N`, then `N = ab` or `N = (a + 2b)(2a + b)` for positive integers `a, b` with
`a² + ab + b²` a perfect square. -/
theorem tile_sqfree_7mod8_form (hsq : Squarefree N) (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N)
    (D : CongruentDissection N) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
      (N = a * b ∨ N = (a + 2 * b) * (2 * a + b)) := by
  by_contra hcon
  exact not_tile_sqfree_7mod8 hsq h8 h3
    (fun a b c ha hb hc hN => hcon ⟨a, b, c, ha, hb, hc, Or.inl hN⟩)
    (fun a b c ha hb hc hN => hcon ⟨a, b, c, ha, hb, hc, Or.inr hN⟩) D

/-- the same, as a statement about tile counts -/
theorem tileCount_sqfree_7mod8_form (hsq : Squarefree N) (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N) (hT : TileCount N) :
    ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧
      (N = a * b ∨ N = (a + 2 * b) * (2 * a + b)) := by
  obtain ⟨D⟩ := hT
  exact tile_sqfree_7mod8_form hsq h8 h3 D

/-- **The statement cannot be improved to an exclusion**: `143` is squarefree, `≡ 7 (mod 8)`, prime to `3`, of the
second form with `(a, b, c) = (3, 5, 7)`, and it is a tile count. -/
theorem sector_sharp_143 : Squarefree 143 ∧ 143 % 8 = 7 ∧ ¬ 3 ∣ 143 ∧ TileCount 143 ∧
    (7 : ℕ) ^ 2 = 3 ^ 2 + 3 * 5 + 5 ^ 2 ∧ (143 : ℕ) = (3 + 2 * 5) * (2 * 3 + 5) := by
  refine ⟨?_, by norm_num, by norm_num, Erdos634.Draft.N143.tileCount_143, by norm_num, by norm_num⟩
  have h : (143 : ℕ) = 11 * 13 := by norm_num
  rw [h]
  exact Nat.squarefree_mul_iff.mpr ⟨by norm_num, (by norm_num : Nat.Prime 11).prime.squarefree,
    (by norm_num : Nat.Prime 13).prime.squarefree⟩

/-! ## The class below `455` -/

theorem sqrt_of_norm {a b c : ℕ} (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    Nat.sqrt (a * a + a * b + b * b) * Nat.sqrt (a * a + a * b + b * b) = a * a + a * b + b * b := by
  have h : a * a + a * b + b * b = c ^ 2 := by rw [hc]; ring
  rw [h, Nat.sqrt_eq']
  ring

/-- **The class below `455`**: among the squarefree `N ≡ 7 (mod 8)` prime to `3` with `N < 455`, the only tile count
is `143`.  (`455 = 13 · 35` is the first value of the class that the theorem does not decide.) -/
theorem sector_below_455 (hsq : Squarefree N) (h8 : N % 8 = 7) (h3 : ¬ 3 ∣ N) (hlt : N < 455) :
    TileCount N ↔ N = 143 := by
  constructor
  · intro hT
    obtain ⟨a, b, c, ha, hb, hc, h | h⟩ := tileCount_sqfree_7mod8_form hsq h8 h3 hT
    · exfalso
      have hsqr := sqrt_of_norm hc
      have hN3 : 0 < (a * b) % 3 := by rw [← h]; omega
      have hN8 : (a * b) % 8 = 7 := by rw [← h]; exact h8
      have hlt' : a * b < 455 := by rw [← h]; exact hlt
      rcases le_total a b with hab | hab
      · have ha22 : a < 22 := by
          by_contra hge
          have hge' : 22 ≤ a := not_lt.mp hge
          have h1 : 22 * 22 ≤ a * b := Nat.mul_le_mul hge' (hge'.trans hab)
          omega
        have hb455 : b < 455 := by
          have h1 : b ≤ a * b := Nat.le_mul_of_pos_left b ha
          omega
        exact chk_ab a ha22 b hb455 hlt' hN8 hN3 hsqr
      · have hb22 : b < 22 := by
          by_contra hge
          have hge' : 22 ≤ b := not_lt.mp hge
          have h1 : 22 * 22 ≤ a * b := Nat.mul_le_mul (hge'.trans hab) hge'
          omega
        have ha455 : a < 455 := by
          have h1 : a ≤ a * b := Nat.le_mul_of_pos_right a hb
          omega
        have e1 : b * a = a * b := Nat.mul_comm b a
        have e2 : b * b + b * a + a * a = a * a + a * b + b * b := by ring
        exact chk_ab b hb22 a ha455 (by rw [e1]; exact hlt') (by rw [e1]; exact hN8) (by rw [e1]; exact hN3)
          (by rw [e2]; exact hsqr)
    · have hsqr := sqrt_of_norm hc
      have hlow : (a + 2) * (2 * a + 1) ≤ (a + 2 * b) * (2 * a + b) := Nat.mul_le_mul (by omega) (by omega)
      have hlow' : (1 + 2 * b) * (2 + b) ≤ (a + 2 * b) * (2 * a + b) := Nat.mul_le_mul (by omega) (by omega)
      have ha16 : a < 16 := by
        by_contra hge
        have hge' : 16 ≤ a := not_lt.mp hge
        have h1 : 18 * 33 ≤ (a + 2) * (2 * a + 1) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have hb16 : b < 16 := by
        by_contra hge
        have hge' : 16 ≤ b := not_lt.mp hge
        have h1 : 33 * 18 ≤ (1 + 2 * b) * (2 + b) := Nat.mul_le_mul (by omega) (by omega)
        omega
      have h143 := chk_f2 a ha16 b hb16 (by rw [← h]; exact hlt) (by rw [← h]; exact h8) (by rw [← h]; omega) hsqr
      rw [h]
      exact h143
  · rintro rfl
    exact Erdos634.Draft.N143.tileCount_143

end Erdos634.Draft.Sqfree7Mod8

#print axioms Erdos634.Draft.Sqfree7Mod8.not_tile_sqfree_7mod8
#print axioms Erdos634.Draft.Sqfree7Mod8.tile_sqfree_7mod8_form
#print axioms Erdos634.Draft.Sqfree7Mod8.sector_sharp_143
#print axioms Erdos634.Draft.Sqfree7Mod8.sector_below_455
