/-
Draft/TwoPrime.lean -- **Twice a prime.**

`not_tile_two_prime`: for a prime `p ≡ 3 (mod 4)`, `p ≥ 7`, no triangle can be cut into `2p` congruent triangles.
`two_prime_tileCount_iff`: for every prime `p`, `2p` is a tile count iff `p = 3` or `p ≢ 3 (mod 4)`
(`4 = 2²`, `6 = 6·1²`, and `2p = (x+y)² + (x−y)²` when `p = x² + y²`).

This is an infinite family of non-tile-counts with a closed form, obtained from the squarefree classification chain
(`ChainIso.chain_gen3_iso`) by proving every arithmetic leaf for `N = 2p` in general instead of evaluating it for one
`N`.  The leaves and why they hold at `N = 2p`:
* `π/3` and `2π/3` tiles on the equilateral triangle, and the `F₁` targets: `N ≡ 2 (mod 4)` (parity of the invariants);
* the scalene targets `F₂`, `F₃`, `F₄`: `N = (x+r)(2x+r)` forces `(x, r) = (1, 1)`, `p = 3`; `4N = 3(…)` forces `3 ∣ p`;
* the isosceles `2π/3` targets (`IsoH9b`): the divisor is `a + 2b = p`, then `b = 2j²` and `c = a + b − 2jt` with
  `0 < t < j`, and `a (j − 2t) = 2jt(2j − t)` with `gcd(a, j) = 1` gives `j ∣ 2t`, impossible;
* base-`α` targets (`IsoQRef`): `Q = e² + 4ed + 2d²` divides `2p`; `Q = 2p` is impossible and `Q = p` forces
  `(e, d) = (1, 2)`, `p = 17 ≡ 1 (mod 4)`;
* the targets `(2α, α, 2β)` (`S2Arith`): `A = 2q² − p'²` divides `8p` and is `≥ 7`, so `p ∣ A`; then
  `B = 3q² − p'²` divides `2X²` with `gcd(B, X) ∣ 2`, so `B` is a power of two, but `B ≥ 11` and `8 ∤ B`;
* the other `3α + 2β = π` targets and `γ = 2α`: `2p` is squarefree;
* commensurable angles, tile similar to the target, right tiles: `p` has odd valuation in `2p` and `p ≡ 3 (mod 4)`.

The chain uses `basebeta_full_unc` (through the squarefree `3α + 2β = π` leaves), like the other composite exclusions.
Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.E60Reduce
import Erdos634.Draft.TileCountFamilies

open scoped Classical

namespace Erdos634.Draft.TwoPrime

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.AllNExclusion Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF Erdos634.Draft.R8Gen2
open Erdos634.Draft.TileCountFamilies
open Erdos634.Geometry.CaseA.LemmaH (HArith)

variable {p : ℕ}

/-! ## Elementary arithmetic of `2p` -/

theorem dvd_two_mul_prime (hp : p.Prime) {Q : ℕ} (hQ : Q ∣ 2 * p) (h3 : 3 ≤ Q) : Q = p ∨ Q = 2 * p := by
  rcases Nat.coprime_or_dvd_of_prime hp Q with hc | hd
  · have h2 : Q ∣ 2 := Nat.Coprime.dvd_of_dvd_mul_right hc.symm hQ
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  · obtain ⟨k, hk⟩ := hd
    rw [hk] at hQ h3
    have hk2 : k ∣ 2 := Nat.dvd_of_mul_dvd_mul_left hp.pos (by rwa [mul_comm 2 p] at hQ)
    have hk2' := Nat.le_of_dvd (by norm_num) hk2
    have hk1 : 1 ≤ k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0] at h3; simp at h3
      · exact h0
    interval_cases k
    · left; rw [hk]; ring
    · right; rw [hk]; ring

/-- `2p = u v` with `2 ≤ u < v` forces `(u, v) = (2, p)`. -/
theorem two_p_factor (hp : p.Prime) {u v : ℕ} (hu : 2 ≤ u) (huv : u < v) (h : 2 * p = u * v) :
    u = 2 ∧ v = p := by
  have hv : v ∣ 2 * p := ⟨u, by rw [h]; ring⟩
  rcases dvd_two_mul_prime hp hv (by omega) with h1 | h1
  · rw [h1] at h
    exact ⟨(Nat.eq_of_mul_eq_mul_right hp.pos h).symm, h1⟩
  · exfalso
    rw [h1] at h
    have h' : 1 * (2 * p) = u * (2 * p) := by rw [one_mul]; exact h
    have := Nat.eq_of_mul_eq_mul_right (by have := hp.pos; omega) h'
    omega

theorem val_two_p (hp : p.Prime) (hp2 : p ≠ 2) : padicValNat p (2 * p) = 1 := by
  haveI := Fact.mk hp
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rw [padicValNat.mul (by norm_num) hp.ne_zero, padicValNat.eq_zero_of_not_dvd h2, padicValNat_self]

theorem val_four_p (hp : p.Prime) (hp2 : p ≠ 2) : padicValNat p (2 * (2 * p)) = 1 := by
  haveI := Fact.mk hp
  have h2 : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rw [padicValNat.mul (by norm_num) (by have := hp.pos; omega), padicValNat.eq_zero_of_not_dvd h2,
    val_two_p hp hp2]

/-- `c r² ≠ M` when `p ∤ c` and `v_p(M)` is odd -/
private theorem ne_of_val {c M : ℕ} (hp : p.Prime) (hc : ¬ p ∣ c) (hM : ¬ Even (padicValNat p M)) (r : ℕ) :
    c * r ^ 2 ≠ M := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  apply hM
  rw [← h]
  by_cases hr : r = 0
  · subst hr; simp
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hc (dvd_zero p)
  rw [padicValNat.mul hc0 (pow_ne_zero 2 hr), padicValNat.pow 2 hr, padicValNat.eq_zero_of_not_dvd hc]
  exact ⟨padicValNat p r, by ring⟩

theorem not_sum_two_sq (hp : p.Prime) (h4 : p % 4 = 3) : ¬ ∃ x y : ℕ, p = x ^ 2 + y ^ 2 := by
  haveI := Fact.mk hp
  intro h
  have := Nat.eq_sq_add_sq_iff.mp h p (Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩) h4
  rw [padicValNat_self] at this
  exact absurd this (by decide)

theorem two_p_not_sum_two_sq (hp : p.Prime) (h4 : p % 4 = 3) : ¬ ∃ x y : ℕ, 2 * p = x ^ 2 + y ^ 2 := by
  intro h
  have hp2 : p ≠ 2 := by rintro rfl; omega
  have := Nat.eq_sq_add_sq_iff.mp h p
    (Nat.mem_primeFactors.mpr ⟨hp, Dvd.intro_left 2 rfl, by have := hp.pos; omega⟩) h4
  rw [val_two_p hp hp2] at this
  exact absurd this (by decide)

theorem harith_two_p (hp : p.Prime) (h7 : 7 ≤ p) : HArith (2 * p) := by
  have hp2 : p ≠ 2 := by omega
  have h1 : ¬ Even (padicValNat p (2 * p)) := by rw [val_two_p hp hp2]; decide
  have h2 : ¬ Even (padicValNat p (2 * (2 * p))) := by rw [val_four_p hp hp2]; decide
  have nd : ∀ c : ℕ, 0 < c → c < 7 → ¬ p ∣ c := fun c hc0 hc h => by
    have := Nat.le_of_dvd hc0 h
    omega
  have nd10 : ¬ p ∣ 10 := fun h => by
    rcases (Nat.Prime.dvd_mul hp).mp (show p ∣ 2 * 5 from h) with h' | h'
    · exact nd 2 (by norm_num) (by norm_num) h'
    · exact nd 5 (by norm_num) (by norm_num) h'
  refine ⟨by have := hp.pos; omega, fun r => ne_of_val hp (nd 2 (by norm_num) (by norm_num)) h1 r,
    fun t => ?_, fun y => ne_of_val hp (nd 3 (by norm_num) (by norm_num)) h2 y, fun t => ?_,
    fun x => ne_of_val hp (nd 3 (by norm_num) (by norm_num)) h1 x, fun r => ne_of_val hp nd10 h1 r⟩
  · have := ne_of_val (c := 1) hp (nd 1 (by norm_num) (by norm_num)) h1 t
    simpa using this
  · have := ne_of_val (c := 1) hp (nd 1 (by norm_num) (by norm_num)) h2 t
    simpa using this

/-! ## The scalene `2π/3` targets `F₂`, `F₃`, `F₄` -/

/-- `2p = (x + r)(2x + r)` has no solution in positive integers for a prime `p ≥ 7` -/
theorem no_f24_factor (hp : p.Prime) (h7 : 7 ≤ p) {x r : ℕ} (hx : 0 < x) (hr : 0 < r)
    (h : 2 * p = (x + r) * (2 * x + r)) : False := by
  obtain ⟨h1, h2⟩ := two_p_factor hp (by omega) (by omega) h
  omega

theorem three_not_dvd (hp : p.Prime) (h7 : 7 ≤ p) (c : ℕ) (hc : ¬ 3 ∣ c) : ¬ 3 ∣ c * p := by
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h'
  · exact hc h'
  · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp h'
    omega

theorem noF2_two_p (hp : p.Prime) (h7 : 7 ≤ p) : NoF2 (2 * p) := by
  refine noF2_of_int (2 * p) ?_ ?_
  · intro z hz
    have h3 : (3 : ℤ) ∣ ((2 * p : ℕ) : ℤ) := ⟨z ^ 2, hz⟩
    have h3' : 3 ∣ 2 * p := by exact_mod_cast h3
    exact three_not_dvd hp h7 2 (by norm_num) h3'
  · intro x r hx hr hN z _
    exact no_f24_factor hp h7 hx hr hN

theorem noF4z_two_p (hp : p.Prime) (h7 : 7 ≤ p) : NoF4z (2 * p) :=
  noF4z_of_int (2 * p) fun x r hx hr hN _ _ => no_f24_factor hp h7 hx hr hN

theorem noF3z_two_p (hp : p.Prime) (h7 : 7 ≤ p) : NoF3z (2 * p) := by
  intro s j z _ _ _ heq _
  have h3 : (3 : ℤ) ∣ ((8 * p : ℕ) : ℤ) := ⟨(s + j) * (s + 3 * j), by push_cast at heq ⊢; linarith⟩
  have h3' : 3 ∣ 8 * p := by exact_mod_cast h3
  exact three_not_dvd hp h7 8 (by norm_num) h3'

/-! ## Base-`α` targets -/

theorem isoQRef_two_p (hp : p.Prime) (h4 : p % 4 = 3) : IsoQRef (2 * p) := by
  apply isoQRef_of_dvd_case
  intro e d m he hd hQ heq
  have hQ7 : 3 ≤ e ^ 2 + 4 * e * d + 2 * d ^ 2 := by
    have h1' : 1 ≤ e ^ 2 := Nat.one_le_pow _ _ he
    have h2' : 1 ≤ d ^ 2 := Nat.one_le_pow _ _ hd
    have h3' : 1 ≤ e * d := Nat.mul_pos he hd
    nlinarith
  rcases dvd_two_mul_prime hp hQ hQ7 with h1 | h1
  · -- Q = p: 2 d = m² (2e + d)
    rw [h1] at heq
    have h2 : 2 * d = m ^ 2 * (2 * e + d) := by
      have : p * (2 * d) = p * (m ^ 2 * (2 * e + d)) := by
        calc p * (2 * d) = 2 * p * d := by ring
          _ = m ^ 2 * ((2 * e + d) * p) := heq
          _ = p * (m ^ 2 * (2 * e + d)) := by ring
      exact Nat.eq_of_mul_eq_mul_left hp.pos this
    have hm1 : m = 1 := by
      have hm0 : m ≠ 0 := by
        rintro rfl
        have : 2 * d = 0 := by rw [h2]; ring
        omega
      have hm2 : m < 2 := by
        by_contra hge
        push Not at hge
        have h4' : 4 ≤ m ^ 2 := by nlinarith
        have := Nat.mul_le_mul_right (2 * e + d) h4'
        linarith
      omega
    have hd2 : d = 2 * e := by
      rw [hm1] at h2
      linarith
    rw [hd2] at h1
    have h17 : p = 17 * e ^ 2 := by rw [← h1]; ring
    have he1 : e = 1 := by
      rcases Nat.eq_or_lt_of_le he with h | h
      · exact h.symm
      · exfalso
        have hdv : e ∣ p := ⟨17 * e, by rw [h17]; ring⟩
        rcases (Nat.dvd_prime hp).mp hdv with h' | h'
        · omega
        · rw [h'] at h17
          have := hp.two_le
          nlinarith
    have hp17 : p = 17 := by rw [he1] at h17; simpa using h17
    omega
  · -- Q = 2p: d = m² (2e + d)
    rw [h1] at heq
    have h2 : d = m ^ 2 * (2 * e + d) := by
      have : 2 * p * d = 2 * p * (m ^ 2 * (2 * e + d)) := by
        calc 2 * p * d = m ^ 2 * ((2 * e + d) * (2 * p)) := heq
          _ = 2 * p * (m ^ 2 * (2 * e + d)) := by ring
      exact Nat.eq_of_mul_eq_mul_left (by have := hp.pos; omega) this
    have hm0 : 1 ≤ m ^ 2 := by
      rcases Nat.eq_zero_or_pos m with h0 | h0
      · exfalso
        rw [h0] at h2
        have : d = 0 := by rw [h2]; ring
        omega
      · exact Nat.one_le_pow _ _ h0
    have := Nat.mul_le_mul_right (2 * e + d) hm0
    linarith

/-! ## Isosceles `2π/3` targets -/

theorem isoH9b_two_p (hp : p.Prime) : IsoH9b (2 * p) := by
  intro a b c k nA ha hb hc hk hcc h3 hcop hdvd hne hbN hkc hpar
  -- the divisor `a + 2b` of `2p` is `p`
  obtain ⟨e, he⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ a + 2 * b by linarith)
  rw [he] at hdvd hne h3 hbN
  have hdvd' : e ∣ 2 * p := by exact_mod_cast hdvd
  have h3' : 3 ≤ e := by exact_mod_cast h3
  have hep : e = p := by
    rcases dvd_two_mul_prime hp hdvd' h3' with h | h
    · exact h
    · exact absurd (by rw [h]) hne
  rw [hep] at hbN he
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  -- `2 b = k²`
  have hk2 : 2 * b = k ^ 2 := by
    have : (p : ℤ) * (2 * b) = (p : ℤ) * k ^ 2 := by push_cast at hbN; linarith
    exact mul_left_cancel₀ hpZ.ne' this
  -- `k = 2 j`, `b = 2 j²`
  have hkev : Even k := by
    have : Even (k ^ 2) := ⟨b, by rw [← hk2]; ring⟩
    exact (Int.even_pow' (by norm_num)).mp this
  obtain ⟨j, hj⟩ := hkev
  have hj0 : 0 < j := by linarith
  have hb2 : b = 2 * j ^ 2 := by
    have : 2 * b = 2 * (2 * j ^ 2) := by rw [hk2, hj]; ring
    linarith
  -- `c − a − b = nA · j`, `nA = 2 u`
  have hcj : c - a - b = nA * j := by
    have : (2 * j) * (c - a - b) = (2 * j) * (nA * j) := by
      have h1 : (j + j) * (c - a - b) = nA * b := by rw [← hj]; exact hkc
      linear_combination h1 + nA * hb2
    exact mul_left_cancel₀ (by linarith : (2 * j : ℤ) ≠ 0) this
  have hnA : (2 : ℤ) ∣ nA := by
    have h2p : (2 : ℤ) ∣ ((2 * p : ℕ) : ℤ) := ⟨p, by push_cast; ring⟩
    have := dvd_add hpar h2p
    simpa using this
  obtain ⟨u, hu⟩ := hnA
  -- bounds: `a < c < a + b`
  have hca : a < c := by
    by_contra h
    push Not at h
    nlinarith [mul_pos ha hb, mul_pos hb hb, mul_le_mul h h hc.le ha.le]
  have hcab : c < a + b := by
    by_contra h
    push Not at h
    nlinarith [mul_pos ha hb, mul_le_mul h h (by linarith : (0 : ℤ) ≤ a + b) hc.le]
  have hcu : c = a + b + 2 * u * j := by rw [hu] at hcj; linarith
  have hu_neg : u < 0 := by
    by_contra h
    push Not at h
    have := mul_nonneg h hj0.le
    linarith
  have hu_lb : -j < u := by
    by_contra h
    push Not at h
    -- `c − a = b + 2uj ≤ 2j² − 2j² = 0`
    have h1 : u * j ≤ (-j) * j := mul_le_mul_of_nonneg_right h hj0.le
    nlinarith [h1, hb2]
  -- the quadratic relation: `a (j + 2u) = −2uj(2j + u)`
  have hq : a * (j + 2 * u) = -(2 * u * j * (2 * j + u)) := by
    have h1 : (a + b + 2 * u * j) ^ 2 = a ^ 2 + a * b + b ^ 2 := by rw [← hcu]; exact hcc
    rw [hb2] at h1
    have h2 : (2 * j) * (a * (j + 2 * u)) = (2 * j) * (-(2 * u * j * (2 * j + u))) := by
      linear_combination h1
    exact mul_left_cancel₀ (by linarith : (2 * j : ℤ) ≠ 0) h2
  -- `gcd(j, a) = 1`, so `j ∣ 2u`
  have hja : IsCoprime j a := by
    have h1 : IsCoprime b a := by
      have : IsCoprime b (a + b * 2) := by rwa [mul_comm b 2]
      exact (IsCoprime.add_mul_left_right_iff).mp this
    rw [hb2] at h1
    have h2 : IsCoprime (j * (2 * j)) a := by
      have : (2 : ℤ) * j ^ 2 = j * (2 * j) := by ring
      rwa [this] at h1
    exact h2.of_mul_left_left
  have hj2u : j ∣ 2 * u := by
    have h1 : j ∣ (2 * u) * a := ⟨-(a + 4 * u * j + 2 * u ^ 2), by linear_combination hq⟩
    exact hja.dvd_of_dvd_mul_right h1
  obtain ⟨w, hw⟩ := hj2u
  -- `−2j < 2u < 0` and `2u = j w` force `w = −1`
  have hw1 : w = -1 := by
    have hlt : j * w < 0 := by rw [← hw]; linarith
    have hgt : -(2 * j) < j * w := by rw [← hw]; linarith
    have hwneg : w < 0 := by
      by_contra h
      push Not at h
      have := mul_nonneg hj0.le h
      linarith
    have hwge : -2 < w := by
      by_contra h
      push Not at h
      have := mul_le_mul_of_nonneg_left h hj0.le
      linarith
    omega
  rw [hw1] at hw
  -- then `j + 2u = 0` and the right-hand side is positive
  have hz : j + 2 * u = 0 := by linarith
  rw [hz] at hq
  have hpos : 0 < -(2 * u * j * (2 * j + u)) := by
    have h1 : 0 < -u := by linarith
    have h2 : 0 < 2 * j + u := by linarith
    have h3 := mul_pos (mul_pos h1 hj0) h2
    have e : -(2 * u * j * (2 * j + u)) = 2 * (-u * j * (2 * j + u)) := by ring
    rw [e]; linarith
  have hz0 : a * 0 = 0 := mul_zero a
  linarith

/-! ## The targets `(2α, α, 2β)` -/

theorem int_odd_prime_dvd_of_dvd_two_mul_sq {r : ℕ} (hr : r.Prime) (hodd : Odd r) {X : ℤ}
    (h : (r : ℤ) ∣ 2 * X ^ 2) : (r : ℤ) ∣ X := by
  have hrZ : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
  rcases hrZ.dvd_mul.mp h with h2 | h2
  · exfalso
    have : r ∣ 2 := by exact_mod_cast h2
    have := Nat.le_of_dvd (by norm_num) this
    have := hr.two_le
    rcases hodd with ⟨t, ht⟩
    omega
  · exact hrZ.dvd_of_dvd_pow h2

theorem s2Arith_two_p (hp : p.Prime) (h7 : 7 ≤ p) : S2Arith (2 * p) := by
  intro p' q S hp' hpq hcop hS heq
  have hd := Erdos634.Draft.CompositeS2Global.s2_dvd (2 * p) p' q S hcop heq
  set A : ℤ := 2 * q ^ 2 - p' ^ 2 with hA
  set B : ℤ := 3 * q ^ 2 - p' ^ 2 with hB
  set X : ℤ := (q - p') * (2 * q + p') with hX
  have hq2 : 2 ≤ q := by omega
  have hp1 : p' ≤ q - 1 := by omega
  have hpsq : p' * p' ≤ (q - 1) * (q - 1) := mul_le_mul hp1 hp1 hp'.le (by linarith)
  have hqq : 2 * q ≤ q * q := by nlinarith
  have hA7 : 7 ≤ A := by rw [hA]; nlinarith
  have hB11 : 11 ≤ B := by rw [hB]; nlinarith
  -- `p ∣ A`
  obtain ⟨An, hAn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ A by linarith)
  have hAn7 : 7 ≤ An := by
    have : (7 : ℤ) ≤ (An : ℤ) := by rw [← hAn]; exact hA7
    exact_mod_cast this
  have hAnd : An ∣ 8 * p := by
    have : (An : ℤ) ∣ ((8 * p : ℕ) : ℤ) := by
      rw [← hAn]
      have : (4 : ℤ) * ((2 * p : ℕ) : ℤ) = ((8 * p : ℕ) : ℤ) := by push_cast; ring
      rw [← this]; exact hd
    exact_mod_cast this
  have hpA : p ∣ An := by
    rcases Nat.coprime_or_dvd_of_prime hp An with hc | hdv
    · exfalso
      have h8 : An ∣ 8 := Nat.Coprime.dvd_of_dvd_mul_right hc.symm hAnd
      have hle := Nat.le_of_dvd (by norm_num) h8
      have hA8 : An = 8 := by
        interval_cases An
        · norm_num at h8
        · rfl
      -- `2q² − p'² = 8` with `0 < p' < q` is impossible
      have hA8' : A = 8 := by rw [hAn, hA8]; norm_num
      rw [hA] at hA8'
      have hq3 : q ≤ 2 := by
        by_contra h
        push Not at h
        have h3q : 3 ≤ q := by omega
        nlinarith
      have hq' : q = 2 := by linarith
      rw [hq'] at hA8'
      have : p' ^ 2 = 0 := by linarith
      have : p' = 0 := by simpa using this
      linarith
    · exact hdv
  obtain ⟨g, hg⟩ := hpA
  have hpZ : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  -- cancel `p`: `2 X² = S² g B`
  have hmain : 2 * X ^ 2 = S ^ 2 * (g : ℤ) * B := by
    have hAg : A = (p : ℤ) * (g : ℤ) := by rw [hAn, hg, Nat.cast_mul]
    have h1 : (p : ℤ) * (2 * X ^ 2) = (p : ℤ) * (S ^ 2 * (g : ℤ) * B) := by
      have h2 : ((2 * p : ℕ) : ℤ) * X ^ 2 = S ^ 2 * A * B := heq
      rw [hAg] at h2
      push_cast at h2
      linarith
    exact mul_left_cancel₀ hpZ.ne' h1
  -- coprimality of `p'`, `q`
  obtain ⟨uu, vv, huv⟩ := hcop
  -- no odd prime divides `B`
  have hBodd : ∀ r : ℕ, r.Prime → Odd r → ¬ (r : ℤ) ∣ B := by
    intro r hr hodd hrB
    have hrZ : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
    have hrX : (r : ℤ) ∣ X := by
      apply int_odd_prime_dvd_of_dvd_two_mul_sq hr hodd
      rw [hmain]
      exact Dvd.dvd.mul_left hrB _
    have hr1 : ¬ (r : ℤ) ∣ 1 := fun h => by
      have : r ∣ 1 := by exact_mod_cast h
      have := Nat.le_of_dvd (by norm_num) this
      have := hr.two_le
      omega
    have hr2 : ¬ (r : ℤ) ∣ 2 := fun h => by
      have : r ∣ 2 := by exact_mod_cast h
      have := Nat.le_of_dvd (by norm_num) this
      have := hr.two_le
      rcases hodd with ⟨t, ht⟩
      omega
    rw [hX] at hrX
    rcases hrZ.dvd_mul.mp hrX with h1 | h1
    · -- `r ∣ q − p'`: `B = 3(q−p')(q+p') + 2p'²`
      have h2 : (r : ℤ) ∣ 2 * p' ^ 2 := by
        have : 2 * p' ^ 2 = B - (q - p') * (3 * (q + p')) := by rw [hB]; ring
        rw [this]
        exact dvd_sub hrB (Dvd.dvd.mul_right h1 _)
      have h3 : (r : ℤ) ∣ p' := by
        rcases hrZ.dvd_mul.mp h2 with h | h
        · exact absurd h hr2
        · exact hrZ.dvd_of_dvd_pow h
      have h4 : (r : ℤ) ∣ q := by
        have := dvd_add h1 h3
        simpa using this
      exact hr1 (by rw [← huv]; exact dvd_add (Dvd.dvd.mul_left h3 _) (Dvd.dvd.mul_left h4 _))
    · -- `r ∣ 2q + p'`: `B = (2q+p')(2q−p') − q²`
      have h2 : (r : ℤ) ∣ q ^ 2 := by
        have : q ^ 2 = (2 * q + p') * (2 * q - p') - B := by rw [hB]; ring
        rw [this]
        exact dvd_sub (Dvd.dvd.mul_right h1 _) hrB
      have h4 : (r : ℤ) ∣ q := hrZ.dvd_of_dvd_pow h2
      have h3 : (r : ℤ) ∣ p' := by
        have := dvd_sub h1 (Dvd.dvd.mul_left h4 2)
        simpa using this
      exact hr1 (by rw [← huv]; exact dvd_add (Dvd.dvd.mul_left h3 _) (Dvd.dvd.mul_left h4 _))
  -- so `B` is a power of two, at least 16
  obtain ⟨Bn, hBn⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ B by linarith)
  have hBn11 : 11 ≤ Bn := by
    have : (11 : ℤ) ≤ (Bn : ℤ) := by rw [← hBn]; exact hB11
    exact_mod_cast this
  have h8B : (8 : ℤ) ∣ B := by
    rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd Bn with ⟨i, hi⟩ | ⟨r, hr, hrd, hrodd⟩
    · have hi3 : 3 ≤ i := by
        by_contra h
        push Not at h
        have h4 : Bn ≤ 4 := by
          rw [hi]
          calc 2 ^ i ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
            _ = 4 := by norm_num
        omega
      have h23 : (8 : ℕ) = 2 ^ 3 := by norm_num
      have : (8 : ℕ) ∣ Bn := by rw [hi, h23]; exact pow_dvd_pow 2 hi3
      rw [hBn]; exact_mod_cast this
    · exfalso
      exact hBodd r hr hrodd (by rw [hBn]; exact_mod_cast hrd)
  -- but `8 ∤ B`: parity of `p'`, `q`
  rcases Int.even_or_odd q with ⟨m, hm⟩ | ⟨m, hm⟩ <;> rcases Int.even_or_odd p' with ⟨n, hn⟩ | ⟨n, hn⟩
  · -- both even: not coprime
    have : (2 : ℤ) ∣ 1 := by
      rw [← huv]
      exact dvd_add (Dvd.dvd.mul_left ⟨n, by rw [hn]; ring⟩ _) (Dvd.dvd.mul_left ⟨m, by rw [hm]; ring⟩ _)
    norm_num at this
  · -- `q` even, `p'` odd: `B` odd
    obtain ⟨w, hw⟩ : ∃ w : ℤ, B = 2 * w + 1 :=
      ⟨6 * m ^ 2 - 2 * n ^ 2 - 2 * n - 1, by rw [hB, hm, hn]; ring⟩
    omega
  · -- `q` odd, `p'` even: `B` odd
    obtain ⟨w, hw⟩ : ∃ w : ℤ, B = 2 * w + 1 :=
      ⟨6 * m ^ 2 + 6 * m + 1 - 2 * n ^ 2, by rw [hB, hm, hn]; ring⟩
    omega
  · -- both odd: `B ≡ 2 (mod 8)`
    obtain ⟨s, hs⟩ := Int.even_mul_succ_self m
    obtain ⟨t, ht⟩ := Int.even_mul_succ_self n
    obtain ⟨w, hw⟩ : ∃ w : ℤ, B = 8 * w + 2 :=
      ⟨3 * s - t, by rw [hB, hm, hn]; linear_combination 12 * hs - 4 * ht⟩
    omega

/-! ## The theorem -/

/-- **Twice a prime `≡ 3 (mod 4)`, `p ≥ 7`, is not a tile count.** -/
theorem not_tile_two_prime (hp : p.Prime) (h4 : p % 4 = 3) (h7 : 7 ≤ p) (D : CongruentDissection (2 * p)) :
    False := by
  have hp2 : p ≠ 2 := by omega
  have hN0 : 0 < 2 * p := by have := hp.pos; omega
  have hsq : Squarefree (2 * p) :=
    Nat.squarefree_mul_iff.mpr ⟨(Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2),
      Nat.prime_two.prime.squarefree, hp.prime.squarefree⟩
  have hmod : (2 * p) % 4 = 2 := by omega
  have hns := two_p_not_sum_two_sq hp h4
  have hodd : ¬ Even (padicValNat p (2 * p)) := by rw [val_two_p hp hp2]; decide
  refine chain_gen3_iso (2 * p) hsq (s1Closed_of_sqfree (2 * p) hsq hN0)
    (s2Closed_of_arith (2 * p) (s2Arith_two_p hp h7))
    (s3Closed_of_isoQRef (2 * p) (isoQRef_two_p hp h4))
    (fun D α a b c hα hd hi =>
      Erdos634.Draft.ThmIsoH9b.thmIso_H9b (2 * p) D (isoH9b_two_p hp) α a b c hα hd hi)
    (fun hS => Erdos634.CaseA.RCompositeE.gapA_of_ellE hS hsq (by omega) (Or.inr hmod) hns
      (harith_two_p hp h7) hp h7 hodd)
    (caseB_of_sumsq (2 * p)
      (fun D μ τ hs => Row2.theoremS_perm_sqfreeE D μ τ hs hsq (by omega) (Or.inr hmod)) hns)
    (caseR_of_H1 (2 * p) (Erdos634.Draft.H1k.h1Right (2 * p)) ?_)
    (Erdos634.Draft.CompositeFinal10.caseG_of_squarefree (2 * p) hsq)
    (gapE60_of_mod4_two (2 * p) hmod) (gapE120_of_mod4_two (2 * p) hmod) (gapF1_of_mod4_two (2 * p) hmod)
    (gapR8_of_arith_z (2 * p) (noF2_two_p hp h7) (noF3z_two_p hp h7) (noF4z_two_p hp h7)) D
  rintro ⟨x, y, hxy⟩
  exact not_sum_two_sq hp h4 ⟨x, y, by omega⟩

/-- **Twice a prime.**  For a prime `p`, `2p` is a tile count iff `p = 3` or `p ≢ 3 (mod 4)`. -/
theorem two_prime_tileCount_iff (hp : p.Prime) : TileCount (2 * p) ↔ (p = 3 ∨ p % 4 ≠ 3) := by
  constructor
  · rintro ⟨D⟩
    by_contra hcon
    push Not at hcon
    obtain ⟨h3, h4⟩ := hcon
    have h7 : 7 ≤ p := by
      by_contra hlt
      push Not at hlt
      interval_cases p <;> omega
    exact not_tile_two_prime hp h4 h7 D
  · rintro (rfl | h4)
    · have h := tileCount_six_sq (k := 1) (by norm_num)
      simpa using h
    · rcases hp.eq_two_or_odd with rfl | hodd
      · exact tileCount_sq (k := 2) (by norm_num)
      · -- `p ≡ 1 (mod 4)`: `p = x² + y²`, `2p = (x+y)² + (x−y)²`
        haveI := Fact.mk hp
        have h1 : p % 4 ≠ 3 := h4
        obtain ⟨x, y, hxy⟩ := Nat.Prime.sq_add_sq (p := p) h1
        have hne : x ≠ y := by
          rintro rfl
          have : 2 ∣ p := ⟨x ^ 2, by rw [← hxy]; ring⟩
          omega
        rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
        · have e : 2 * p = (x + y) * (x + y) + (y - x) * (y - x) := by
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
            rw [← hxy]
            have : x + d + 1 - x = d + 1 := by omega
            rw [this]; ring
          rw [e]
          exact tileCount_two_squares _ _ (by omega) (by omega)
        · have e : 2 * p = (x + y) * (x + y) + (x - y) * (x - y) := by
            obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hlt
            rw [← hxy]
            have : y + d + 1 - y = d + 1 := by omega
            rw [this]; ring
          rw [e]
          exact tileCount_two_squares _ _ (by omega) (by omega)

end Erdos634.Draft.TwoPrime

#print axioms Erdos634.Draft.TwoPrime.not_tile_two_prime
#print axioms Erdos634.Draft.TwoPrime.two_prime_tileCount_iff
