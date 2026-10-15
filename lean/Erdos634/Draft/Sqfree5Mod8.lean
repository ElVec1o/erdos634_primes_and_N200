/-
Draft/Sqfree5Mod8.lean -- **the sector `N ≡ 5 (mod 8)`: squarefree, `3 ∤ N`.**

`tile_sqfree_5mod8_form`: if a triangle is cut into `N` congruent triangles, `N` squarefree, `N % 8 = 5`, `3 ∤ N`,
then one of the following holds:

* `N = x² + y²` (the classical family);
* `N ((q − p)(2q + p))² = S² (2q² − p²)(3q² − p²)` for coprime `0 < p < q` and `S ≠ 0` (the target
  `(2α, α, 2β)` of a tile with `3α + 2β = π`);
* `N = d (2e + d)(e² + 4ed + 2d²)` with `gcd(e, e + d) = 1`, that is `N = (f² − e²)(2f² − e²)` with `f = e + d`
  (the isosceles target with base angles `α` of the member `(e, f)`, at the scale `f − e`).

So in this residue class every row of the tiles with an angle `2π/3` or `π/3` is closed, and of the tiles with
`3α + 2β = π` only two rows remain.  With `Sqfree3Mod8` (no tile count) and `Sqfree7Mod8` (two rows of the `2π/3`
tiles), three of the four odd residue classes modulo `8` are reduced, for squarefree `N` prime to `3`.

The class contains tile counts of the first two kinds: sums of two squares, and `77 = 7 · 11` (`sector5_sharp_77`;
`p = 1`, `q = 2`).  Whether a value of the third kind is a tile count is not known (`517 = 11 · 47` is the first one
in the class).

Proof: the chain `ChainIso.chain_gen3_iso`, as in `Sqfree7Mod8`.  Isosceles `2π/3` targets need `N ≡ 1`; `F₂` needs
`N ≡ 7`, `F₄` needs `N ≡ 1`, `F₃` needs `3 ∣ N`; the discriminants of the equilateral pairs are `≡ 20 (mod 32)`
(`2π/3`) or `16 (4u² − N)` with `4u² − N ≡ 3 (mod 4)` (`π/3`); the discriminant of an `F₁` pair is not a square
modulo `64` (`Sqfree5Mod8Chk.z64_f1`).  Uses `basebeta_full_unc`.

Composite-N theorem.  NOT prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.Sqfree7Mod8
import Erdos634.Draft.Sqfree5Mod8Chk
import Erdos634.Draft.S2GAssemble

open scoped Classical

namespace Erdos634.Draft.Sqfree5Mod8

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.AllNExclusion Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF Erdos634.Draft.R8Gen2
open Erdos634.Draft.TileCountFamilies
open Erdos634.Geometry.CaseA.LemmaH (HArith)
open Erdos634.Draft.F1PairCert (F1Pair f1Pair_of_arith)
open Erdos634.Draft.Sqfree3Mod8 (z8_odd_sq z8_sq_ne5 z4_sumsq z4_sq_ne3 two_odd_sq prime_ge7 odd_cast_sq
  noF3z_3mod8 s3inst_of_not_dvd)
open Erdos634.Draft.Sqfree7Mod8 (z8_prod7)
open Erdos634.Draft.Sqfree5Mod8Chk (z64_f1)

variable {N : ℕ}

/-! ## Finite checks -/

theorem z8_sq_ne10 : ∀ x : ZMod 8, x ^ 2 ≠ 2 * 5 := by decide
theorem z8_five_ne_one : (5 : ZMod 8) ≠ 1 := by decide

theorem z8_f2 : ∀ X R Z : ZMod 8, (5 : ZMod 8) = (X + R) * (2 * X + R) → (5 : ZMod 8) ≠ 3 * Z ^ 2 - X ^ 2 := by
  decide +kernel

theorem z8_f4 : ∀ X R Z : ZMod 8, (5 : ZMod 8) = (X + R) * (2 * X + R) → Z ^ 2 ≠ X ^ 2 + X * R + R ^ 2 := by
  decide +kernel

theorem cast8 (h8 : N % 8 = 5) : ((N : ℕ) : ZMod 8) = 5 := by
  rw [← ZMod.natCast_mod, h8]
  rfl

theorem cast4 (h8 : N % 8 = 5) : ((N : ℕ) : ZMod 4) = 1 := by
  have h4 : N % 4 = 1 := by omega
  rw [← ZMod.natCast_mod, h4]
  rfl

theorem odd_int (h8 : N % 8 = 5) : Odd (N : ℤ) := ⟨((N / 2 : ℕ) : ℤ), by omega⟩

/-! ## The forms `c r²`, a large prime -/

theorem harith_5mod8 (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N) : HArith N := by
  have hc := cast8 h8
  refine ⟨by omega, fun r h => ?_, fun t h => ?_, fun y h => ?_, fun t h => ?_, fun x h => ?_, fun r h => ?_⟩
  · omega
  · have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    rw [hc] at h'
    exact z8_sq_ne5 _ h'
  · omega
  · have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    rw [hc] at h'
    exact z8_sq_ne10 _ h'
  · omega
  · omega

theorem exists_prime_ge7 (hsq : Squarefree N) (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N) (h5N : N ≠ 5) :
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

/-! ## Isosceles targets with a `2π/3` tile -/

theorem isoH9b_5mod8 (h8 : N % 8 = 5) : IsoH9b N := by
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
    have h51 : (5 : ZMod 8) = 1 := by
      linear_combination hn8 + ((b : ZMod 8) * n₁) * e3 + e2 - ((a : ZMod 8) * n₁) * hB2
    exact z8_five_ne_one h51

/-! ## The scalene `2π/3` targets -/

theorem noF2_5mod8 (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N) : NoF2 N := by
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

theorem noF4z_5mod8 (h8 : N % 8 = 5) : NoF4z N := by
  have hc := cast8 h8
  refine noF4z_of_int N ?_
  intro x r _ _ hN z hz
  have h1 := congrArg (Nat.cast : ℕ → ZMod 8) hN
  push_cast at h1
  rw [hc] at h1
  have h2 := congrArg (Int.cast : ℤ → ZMod 8) hz
  push_cast at h2
  exact z8_f4 (x : ZMod 8) (r : ZMod 8) (z : ZMod 8) (by linear_combination h1) (by linear_combination h2)

/-! ## Equilateral pairs and `F₁` pairs -/

/-- factors of `3N`, `N ≡ 5 (mod 8)`: their sum is divisible by `8` -/
theorem factors_sum8 (h8 : N % 8 = 5) (s t : ℤ) (hprod : s * t = 3 * (N : ℤ)) : (8 : ℤ) ∣ s + t := by
  have hc := cast8 h8
  have hp8 := congrArg (Int.cast : ℤ → ZMod 8) hprod
  push_cast at hp8
  rw [hc] at hp8
  have h15 : (3 : ZMod 8) * 5 = 7 := by decide
  rw [h15] at hp8
  have hs8 := z8_prod7 _ _ hp8
  have h0 : ((s + t : ℤ) : ZMod 8) = 0 := by
    push_cast
    exact hs8
  have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (s + t) 8).mp h0
  exact_mod_cast h1

/-- the discriminant of a `π/3` pair on the equilateral triangle is not a square -/
theorem e60_disc_not_sq (h8 : N % 8 = 5) (m₁ m₂ : ℤ)
    (hprod : m₁ * m₂ = 3 * (N : ℤ)) : ¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (N : ℤ)) := by
  obtain ⟨u, hu⟩ := factors_sum8 h8 m₁ m₂ hprod
  rintro ⟨r, hr⟩
  rw [hu] at hr
  have hre : Even r := by
    have h1 : Even (r * r) := ⟨32 * u ^ 2 - 8 * (N : ℤ), by rw [← hr]; ring⟩
    rcases Int.even_mul.mp h1 with h | h <;> exact h
  obtain ⟨r₁, rfl⟩ := hre
  have hr1 : r₁ ^ 2 = 16 * u ^ 2 - 4 * (N : ℤ) := by
    have h1 : 4 * r₁ ^ 2 = 4 * (16 * u ^ 2 - 4 * (N : ℤ)) := by linear_combination (-1 : ℤ) * hr
    exact mul_left_cancel₀ (by norm_num) h1
  have hre1 : Even r₁ := by
    have h1 : Even (r₁ ^ 2) := ⟨8 * u ^ 2 - 2 * (N : ℤ), by rw [hr1]; ring⟩
    exact (Int.even_pow' two_ne_zero).mp h1
  obtain ⟨r₂, rfl⟩ := hre1
  have hr2 : r₂ ^ 2 = 4 * u ^ 2 - (N : ℤ) := by
    have h1 : 4 * r₂ ^ 2 = 4 * (4 * u ^ 2 - (N : ℤ)) := by linear_combination hr1
    exact mul_left_cancel₀ (by norm_num) h1
  have h4 := congrArg (Int.cast : ℤ → ZMod 4) hr2
  push_cast at h4
  have h40 : (4 : ZMod 4) = 0 := by decide
  rw [h40, zero_mul, zero_sub, cast4 h8] at h4
  exact z4_sq_ne3 _ (h4.trans (by decide))

/-- the pairs of the `2π/3` tiles on the equilateral triangle -/
theorem e120_pairs (hsq : Squarefree N) (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N) :
    ∀ s t : ℤ, 1 ≤ s → s ≤ N → 1 ≤ t → t ≤ N → s * t = 3 * (N : ℤ) →
      ¬ IsSquare ((t - s) ^ 2 + 16 * (N : ℤ)) ∧ ∀ r : ℤ, 0 ≤ r → 2 * (N : ℤ) ≠ r * (s + t) := by
  intro s t hs1 _ ht1 _ hprod
  constructor
  · have hc := cast8 h8
    have hNodd := odd_int h8
    obtain ⟨u, hu⟩ := factors_sum8 h8 s t hprod
    have h3odd : Odd (3 : ℤ) := ⟨1, by norm_num⟩
    have hOst : Odd (s * t) := by
      rw [hprod]
      exact h3odd.mul hNodd
    obtain ⟨hOs, -⟩ := Int.odd_mul.mp hOst
    rintro ⟨r, hr⟩
    have hts : t - s = 2 * (4 * u - s) := by linarith
    have hOw : Odd (4 * u - s) := Even.sub_odd ⟨2 * u, by ring⟩ hOs
    rw [hts] at hr
    have hre : Even r := by
      have h1 : Even (r * r) := ⟨2 * (4 * u - s) ^ 2 + 8 * (N : ℤ), by rw [← hr]; ring⟩
      rcases Int.even_mul.mp h1 with h | h <;> exact h
    obtain ⟨r₁, rfl⟩ := hre
    have hr1 : r₁ ^ 2 = (4 * u - s) ^ 2 + 4 * (N : ℤ) := by
      have h1 : 4 * r₁ ^ 2 = 4 * ((4 * u - s) ^ 2 + 4 * (N : ℤ)) := by linear_combination (-1 : ℤ) * hr
      exact mul_left_cancel₀ (by norm_num) h1
    have h8' := congrArg (Int.cast : ℤ → ZMod 8) hr1
    push_cast at h8'
    have hw2 := odd_cast_sq hOw
    push_cast at hw2
    rw [hw2, hc] at h8'
    exact z8_sq_ne5 _ (h8'.trans (by decide))
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

/-- every `F₁` pair has a non-square discriminant (not a square modulo `64`) -/
theorem f1Pair_5mod8 (h8 : N % 8 = 5) : ∀ Ma Mb : ℕ, 1 < Ma → Ma < Mb → Ma * Mb = N → F1Pair N Ma Mb := by
  intro Ma Mb h1 hlt hprod
  have hc := cast8 h8
  have hp8 : (Ma : ZMod 8) * (Mb : ZMod 8) = 5 := by
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
  refine f1Pair_of_arith N Ma Mb (j - i) (by omega) (by omega) hprod (by omega) ?_ ?_
  · rintro ⟨r, hr⟩
    have hN64 : (N : ZMod 64) = (Ma : ZMod 64) * Mb := by
      rw [← hprod, Nat.cast_mul]
    have h8N : (8 : ZMod 64) * (N : ZMod 64) = 40 := by
      have h1' : 8 * N = 64 * (N / 8) + 40 := by omega
      have h2 := congrArg (Nat.cast : ℕ → ZMod 64) h1'
      push_cast at h2
      have h64z : (64 : ZMod 64) = 0 := by decide
      rw [h64z, zero_mul, zero_add] at h2
      exact h2
    have h64 := congrArg (Int.cast : ℤ → ZMod 64) hr
    push_cast at h64
    rw [hN64] at h64 h8N
    exact z64_f1 (Ma : ZMod 64) (Mb : ZMod 64) (r : ZMod 64) h8N (by linear_combination (-1 : ZMod 64) * h64)
  · intro h
    have h' := congrArg (Nat.cast : ℕ → ZMod 8) h
    push_cast at h'
    have h2 : (1 : ZMod 8) + 1 = 4 * 5 := by linear_combination h' - hA2 - hB2 + 4 * hp8
    exact absurd h2 (by decide)

/-! ## The leaves of the chain -/

/-- the base-`α` leaf, given that `N` is not of the third form -/
theorem s3Closed_5mod8 (hsq : Squarefree N) (hN0 : 0 < N)
    (hBA : ∀ e d : ℕ, 1 ≤ e → 1 ≤ d → Nat.Coprime e (e + d) →
      N ≠ d * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) : S3Closed N := by
  refine s3Closed_of_inst N ?_
  intro e d m he hd hcop heq
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · exfalso
      rw [h] at heq
      have hNd : N * d = 0 := by rw [heq]; ring
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
    have hrr : r * r ∣ N := ⟨d * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2), by rw [h']; ring⟩
    have hr1 : r = 1 := Nat.isUnit_iff.mp (hsq r hrr)
    rw [hr1] at h'
    exact hBA e d he hd hcop (by rw [h']; ring)
  · have hnd : ¬ (e + d - e) ∣ m := by rwa [Nat.add_sub_cancel_left]
    intro N' D' a0 a1 a2 a3
    exact s3inst_of_not_dvd m e (e + d) he (by omega) hcop hm hnd D' a0 a1 a2 a3

theorem gapE60_5mod8 (h8 : N % 8 = 5) : GapE60 N := by
  intro D α a b c hα h hE
  obtain ⟨m₁, m₂, -, -, -, -, -, -, hS1, hS2, -, hprod, -, -⟩ := Row5.theoremE_sixty D hα h hE
  exact Erdos634.Draft.E60Irr.e60Pair_of_not_isSquare N m₁ m₂ (e60_disc_not_sq h8 m₁ m₂ hprod) D α a b c
    hα h hE hS1 hS2

theorem gapE120_5mod8 (hsq : Squarefree N) (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N) : GapE120 N :=
  Erdos634.Draft.CompositeE5Gen.gapE120_of_pairs N (by omega) (e120_pairs hsq h8 h3)

theorem gapF1_5mod8 (h8 : N % 8 = 5) (h7 : 6 < N) : GapF1 N :=
  Erdos634.Draft.CompositeF1Gen.gapF1_of_MaGt1 N h7
    (Erdos634.Draft.F1PairCert.f1MaGt1_of_pairs N (f1Pair_5mod8 h8))

/-! ## The theorem -/

/-- **Squarefree `N ≡ 5 (mod 8)`, `3 ∤ N`, of none of the three forms: not a tile count.** -/
theorem not_tile_sqfree_5mod8 (hsq : Squarefree N) (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N)
    (hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2) (hQP : S2Arith N)
    (hBA : ∀ e d : ℕ, 1 ≤ e → 1 ≤ d → Nat.Coprime e (e + d) →
      N ≠ d * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2))
    (D : CongruentDissection N) : False := by
  have h5N : N ≠ 5 := by
    rintro rfl
    exact hns ⟨1, 2, by norm_num⟩
  have h13N : N ≠ 13 := by
    rintro rfl
    exact hns ⟨2, 3, by norm_num⟩
  have h29 : 21 ≤ N := by omega
  have hN0 : 0 < N := by omega
  obtain ⟨ℓ, hℓ, hℓ7, hodd⟩ := exists_prime_ge7 hsq h8 h3 h5N
  exact chain_gen3_iso N hsq (s1Closed_of_sqfree N hsq hN0)
    (s2Closed_of_arith N hQP)
    (s3Closed_5mod8 hsq hN0 hBA)
    (fun D α a b c hα hd hi =>
      Erdos634.Draft.ThmIsoH9b.thmIso_H9b N D (isoH9b_5mod8 h8) α a b c hα hd hi)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq (by omega) (Or.inl (by omega)) hns
      (harith_5mod8 h8 h3) hℓ hℓ7 hodd)
    (caseB_of_sumsq N
      (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq (by omega) (Or.inl (by omega))) hns)
    (caseR_of_odd N (by omega))
    (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree N hsq)
    (gapE60_5mod8 h8) (gapE120_5mod8 hsq h8 h3) (gapF1_5mod8 h8 (by omega))
    (gapR8_of_arith_z N (noF2_5mod8 h8 h3) (noF3z_3mod8 h3) (noF4z_5mod8 h8)) D

/-- **The sector `N ≡ 5 (mod 8)`.**  If a triangle is cut into `N` congruent triangles, with `N` squarefree,
`N ≡ 5 (mod 8)` and `3 ∤ N`, then `N` is a sum of two squares, or `N` satisfies the equation of the target
`(2α, α, 2β)`, or `N = d (2e + d)(e² + 4ed + 2d²)`. -/
theorem tile_sqfree_5mod8_form (hsq : Squarefree N) (h8 : N % 8 = 5) (h3 : ¬ 3 ∣ N)
    (D : CongruentDissection N) :
    (∃ x y : ℕ, N = x ^ 2 + y ^ 2) ∨
    (∃ p q S : ℤ, 0 < p ∧ p < q ∧ IsCoprime p q ∧ S ≠ 0 ∧
      (N : ℤ) * ((q - p) * (2 * q + p)) ^ 2 = S ^ 2 * (2 * q ^ 2 - p ^ 2) * (3 * q ^ 2 - p ^ 2)) ∨
    (∃ e d : ℕ, 1 ≤ e ∧ 1 ≤ d ∧ Nat.Coprime e (e + d) ∧
      N = d * (2 * e + d) * (e ^ 2 + 4 * e * d + 2 * d ^ 2)) := by
  by_contra hcon
  refine not_tile_sqfree_5mod8 hsq h8 h3 (fun h => hcon (Or.inl h)) ?_ ?_ D
  · intro p q S hp hpq hcop hS heq
    exact hcon (Or.inr (Or.inl ⟨p, q, S, hp, hpq, hcop, hS, heq⟩))
  · intro e d he hd hcop hN
    exact hcon (Or.inr (Or.inr ⟨e, d, he, hd, hcop, hN⟩))

/-- **The statement cannot be improved to "sum of two squares"**: `77` is squarefree, `≡ 5 (mod 8)`, prime to `3`,
not a sum of two squares, and a tile count (the target `(2α, α, 2β)` with `p = 1`, `q = 2`). -/
theorem sector5_sharp_77 : Squarefree 77 ∧ 77 % 8 = 5 ∧ ¬ 3 ∣ 77 ∧ TileCount 77 ∧
    (77 : ℤ) * ((2 - 1) * (2 * 2 + 1)) ^ 2 = 5 ^ 2 * (2 * 2 ^ 2 - 1 ^ 2) * (3 * 2 ^ 2 - 1 ^ 2) := by
  refine ⟨?_, by norm_num, by norm_num, ?_, by norm_num⟩
  · have h : (77 : ℕ) = 7 * 11 := by norm_num
    rw [h]
    exact Nat.squarefree_mul_iff.mpr ⟨by norm_num, (by norm_num : Nat.Prime 7).prime.squarefree,
      (by norm_num : Nat.Prime 11).prime.squarefree⟩
  · show Nonempty (CongruentDissection 77)
    have h := Erdos634.Draft.S2G.s2_family_gen 1 2 le_rfl (by norm_num)
    simpa using h

end Erdos634.Draft.Sqfree5Mod8

#print axioms Erdos634.Draft.Sqfree5Mod8.not_tile_sqfree_5mod8
#print axioms Erdos634.Draft.Sqfree5Mod8.tile_sqfree_5mod8_form
#print axioms Erdos634.Draft.Sqfree5Mod8.sector5_sharp_77
