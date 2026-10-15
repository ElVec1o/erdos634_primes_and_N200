import Mathlib.Tactic
import Erdos634.SpectrumZhang
import Erdos634.AdmissibleSpectrum
import Erdos634.SpectrumLattice

/-!
# `thm:spectrum` (converse and mirror/F1 forms), `thm:admissible` (arithmetic half), `thm:lattice` (paper form)

## What is proved here

* `b_dvd_k` -- the whole `p`-adic converse of the spectrum theorem collapses to one statement:
  `X ∣ 3ak`, `Y ∣ 3ak`, `A ≡ B (mod 2)` (with `A = 3ak/X`, `B = 3ak/Y`) imply `b ∣ k`.
  (Bezout for `gcd(c, b-a) = 1`, then a parity split; no valuations.)  This is a shorter
  proof than the `p`-adic one; the conclusion is the same (`e ∣ w`, i.e. `N = m² b (a+2b)`).
* `spectrum_alpha_iff` : the base-`α` clause as an `↔` (both halves), with the invariants
  `M_α, M_β` and the area equation.
* `spectrum_beta_iff` : the mirror clause (`a ↔ b`).
* `spectrum_F1_iff`   : the `F₁` clause, `N = m² b (a+b)`.
* `admissible_arith`  : the arithmetic half of `thm:admissible` (scale `k = d e w`, `N = d w² (a+2b)`,
  and, GIVEN an integer invariant value `M` with `M·b = k(c-a-b)` and `M ≡ N (mod 2)`, the clauses
  `e ∣ w(c-a-b)` and `w(c-a-b)/e ≡ N (mod 2)`).
* `lattice_paper` : `thm:lattice` stated with the paper's own data (`r = c-a-b` a NEGATIVE integer,
  `g = gcd(e,r)`, `e₁ = e/g`, `T`, `E`), as a set equality of counts.

## What is NOT proved here (exactly)

The hypothesis side of `thm:admissible` ("every `N`-tiling of the base-`α` isosceles target has area
equation `N b = k²(a+2b)` and an integer invariant `M = k(c-a-b)/b ≡ N`") is geometry: it is the
integrality corollary (`Paper.cor_int_anchored`) applied to the base-`α` target, which needs the
target's boundary flux `Φ(∂ABC) = k(c-a-b)`-type value computed from the corner/side data of a real
`CongruentDissection`.  That passage is not in Lean.  Here those are HYPOTHESES (`harea`, `hM`), so the
Lean statements are arithmetic converses/assemblies, WEAKER than the tiling-level wording and STRONGER
only in giving `↔` where the paper's proof only sketches the mirror.
-/

namespace Erdos634.Draft.FDDSpectrum

/-- `2 ∣ x` in `ℤ` iff `x = 0` in `ZMod 2`. -/
theorem two_dvd_iff (x : ℤ) : (2 : ℤ) ∣ x ↔ ((x : ZMod 2) = 0) := by
  have := ZMod.intCast_zmod_eq_zero_iff_dvd x 2
  simpa using this.symm

/-- Any common prime factor of `c` and `b - a` is impossible for a primitive `120°` triple. -/
theorem no_common_prime (a b c : ℤ) (hcop : IsCoprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (p : ℕ) (hp : p.Prime) (h1 : (p : ℤ) ∣ c) (h2 : (p : ℤ) ∣ b - a) : False := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have key : 3 * a * b = c ^ 2 - (b - a) ^ 2 := by linear_combination -hc
  have hd : (p : ℤ) ∣ 3 * a * b := by
    rw [key]; exact dvd_sub (dvd_pow h1 (by norm_num)) (dvd_pow h2 (by norm_num))
  have hboth : (p : ℤ) ∣ a → False := by
    intro ha
    have hb : (p : ℤ) ∣ b := by have := dvd_add h2 ha; simpa using this
    exact hpp.not_unit (hcop.isUnit_of_dvd' ha hb)
  have hboth' : (p : ℤ) ∣ b → False := by
    intro hb
    have ha : (p : ℤ) ∣ a := by have := dvd_sub hb h2; simpa using this
    exact hboth ha
  rcases hpp.dvd_or_dvd hd with h3 | hb
  · rcases hpp.dvd_or_dvd h3 with h3 | ha
    · have h3' : p ∣ 3 := by exact_mod_cast h3
      have hp3 : p = 3 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3'
      subst hp3
      obtain ⟨s, hs⟩ := h1
      obtain ⟨t, ht⟩ := h2
      -- c² = (b-a)² + 3ab ⟹ 9 ∣ 3ab ⟹ 3 ∣ ab
      have h9 : (3 : ℤ) * (a * b) = 9 * (s ^ 2 - t ^ 2) := by
        have : 3 * a * b = c ^ 2 - (b - a) ^ 2 := key
        rw [hs, ht] at this; push_cast at this; linear_combination this
      have h3ab : (3 : ℤ) ∣ a * b := ⟨s ^ 2 - t ^ 2, by linarith⟩
      rcases hpp.dvd_or_dvd h3ab with ha | hb
      · exact hboth ha
      · exact hboth' hb
    · exact hboth ha
  · exact hboth' hb

theorem coprime_c_ba (a b c : ℤ) (hcop : IsCoprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    IsCoprime c (b - a) := by
  rw [Int.isCoprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hg : ((Int.gcd c (b - a) : ℕ) : ℤ) ∣ c := Int.gcd_dvd_left c (b - a)
  have hg2 : ((Int.gcd c (b - a) : ℕ) : ℤ) ∣ b - a := Int.gcd_dvd_right c (b - a)
  have hpg : (p : ℤ) ∣ ((Int.gcd c (b - a) : ℕ) : ℤ) := Int.natCast_dvd_natCast.mpr hpd
  exact no_common_prime a b c hcop hc p hp (hpg.trans hg) (hpg.trans hg2)

/-- **Key lemma (the whole `p`-adic converse).** `X ∣ 3ak`, `Y ∣ 3ak` (`A X = 3ak`, `B Y = 3ak`) and
`A ≡ B (mod 2)` force `b ∣ k`. -/
theorem b_dvd_k (a b c k A B : ℤ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c) (hcop : IsCoprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hA : A * (c + a - b) = 3 * a * k) (hB : B * (c + b - a) = 3 * a * k)
    (hpar : (2 : ℤ) ∣ A - B) : b ∣ k := by
  have hXpos : 0 < c + a - b := by nlinarith
  have hYpos : 0 < c + b - a := by nlinarith
  have hXY : (c + a - b) * (c + b - a) = 3 * a * b := by linear_combination hc
  obtain ⟨u, v, huv⟩ := coprime_c_ba a b c hcop hc
  -- Bezout: (u-v) X + (u+v) Y = 2
  have hbez : (u - v) * (c + a - b) + (u + v) * (c + b - a) = 2 := by linear_combination 2 * huv
  -- 3ab * W = 6ak
  set W : ℤ := (u - v) * B + (u + v) * A with hW
  have hW6 : 3 * a * b * W = 2 * (3 * a * k) := by
    have e1 : (u - v) * (c + a - b) * (3 * a * k) = (u - v) * (c + a - b) * (B * (c + b - a)) := by
      rw [hB]
    have e2 : (u + v) * (c + b - a) * (3 * a * k) = (u + v) * (c + b - a) * (A * (c + a - b)) := by
      rw [hA]
    have : 2 * (3 * a * k) = ((u - v) * (c + a - b) + (u + v) * (c + b - a)) * (3 * a * k) := by
      rw [hbez]
    rw [this, add_mul, e1, e2, hW, ← hXY]; ring
  have hbW : b * W = 2 * k := by
    have h3a : (3 * a) ≠ 0 := by positivity
    have : 3 * a * (b * W) = 3 * a * (2 * k) := by linear_combination hW6
    exact mul_left_cancel₀ h3a this
  have hodd_dvd : (b ∣ 2 * k) → (b % 2 = 1) → b ∣ k := by
    intro h hodd
    have hcb : IsCoprime b 2 := by
      obtain ⟨t, ht⟩ : ∃ t, b = 2 * t + 1 := ⟨b / 2, by omega⟩
      exact ⟨1, -t, by rw [ht]; ring⟩
    exact hcb.dvd_of_dvd_mul_left h
  rcases Int.even_or_odd W with ⟨j, hj⟩ | hWodd
  · -- W = j + j
    have h2k : (2 : ℤ) * k = 2 * (b * j) := by rw [← hbW, hj]; ring
    exact ⟨j, by linarith⟩
  · -- W odd: 2A = Y W, 2B = X W, A - B = (b-a) W
    have h2A : 2 * A = (c + b - a) * W := by
      have : (c + a - b) * (2 * A) = (c + a - b) * ((c + b - a) * W) := by
        linear_combination 2 * hA - hW6 - W * hXY
      exact mul_left_cancel₀ hXpos.ne' this
    have h2B : 2 * B = (c + a - b) * W := by
      have : (c + b - a) * (2 * B) = (c + b - a) * ((c + a - b) * W) := by
        linear_combination 2 * hB - hW6 - W * hXY
      exact mul_left_cancel₀ hYpos.ne' this
    have hAB2 : 2 * (A - B) = 2 * ((b - a) * W) := by linear_combination h2A - h2B
    have hAB : A - B = (b - a) * W := by linarith
    have h2 : (2 : ℤ) ∣ (b - a) * W := hAB ▸ hpar
    have hWo : ¬ (2 : ℤ) ∣ W := by
      rintro ⟨q, hq⟩; rcases hWodd with ⟨t, ht⟩; omega
    have hba : (2 : ℤ) ∣ b - a := by
      rcases Int.prime_two.dvd_or_dvd h2 with h | h
      · exact h
      · exact absurd h hWo
    -- a, b both odd
    have hbodd : b % 2 = 1 := by
      by_contra hbe
      have hbe' : (2 : ℤ) ∣ b := by omega
      have hae : (2 : ℤ) ∣ a := by have := dvd_sub hbe' hba; simpa using this
      exact Int.prime_two.not_unit (hcop.isUnit_of_dvd' hae hbe')
    exact hodd_dvd ⟨W, by linarith⟩ hbodd

/-! ## `thm:spectrum`, paper form -/

/-- ZMod 2 parity identities used in the "every Zhang member is admissible" halves. -/
theorem parity_alpha_a : ∀ A B C M : ZMod 2, C = A + B + A * B →
    (C - A - B) * M - M ^ 2 * B * (A + 2 * B) = 0 := by decide

theorem parity_alpha_b : ∀ A B C M : ZMod 2, C = A + B + A * B →
    (C + A + B) * M - M ^ 2 * B * (A + 2 * B) = 0 := by decide

theorem parity_F1a : ∀ A B C M : ZMod 2, C = A + B + A * B →
    (C - A) * M - M ^ 2 * B * (A + B) = 0 := by decide

theorem parity_F1b : ∀ A B C M : ZMod 2, C = A + B + A * B →
    (C + A) * M - M ^ 2 * B * (A + B) = 0 := by decide

theorem pos_c (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) : 0 < c := by
  rcases Nat.eq_zero_or_pos c with h | h
  · subst h; have := Nat.mul_pos ha hb; nlinarith
  · exact h

/-- Common set-up: from `k > 0` and `k = b·j` (over `ℤ`) get a natural `m > 0` with `k = b·m`. -/
theorem nat_scale (b k : ℕ) (hb : 0 < b) (hk : 0 < k) (j : ℤ) (hj : (k : ℤ) = b * j) :
    ∃ m : ℕ, 0 < m ∧ k = b * m := by
  have hjpos : 0 < j := by
    by_contra h; push Not at h
    have : (b : ℤ) * j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) h
    have : (0 : ℤ) < k := by exact_mod_cast hk
    linarith
  refine ⟨j.toNat, by omega, ?_⟩
  have : (k : ℤ) = b * (j.toNat : ℤ) := by rw [Int.toNat_of_nonneg hjpos.le]; exact hj
  exact_mod_cast this

/-- **`thm:spectrum`, base-`α` clause.**  `(a,b,c)` a primitive `120°`-triple.  The counts `N` for
which some scale `k ≥ 1` satisfies the area equation `N b = k²(a+2b)` and the two invariant counts
`M_α = k(2b+a-2c)/(c+a-b)`, `M_β = k(2b+a+2c)/(c+b-a)` are integers `≡ N (mod 2)` are exactly
`N = m² b (a+2b)`, `m ≥ 1`. -/
theorem spectrum_alpha_iff (a b c N : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (∃ k : ℕ, 0 < k ∧ N * b = k ^ 2 * (a + 2 * b) ∧
      ∃ Ma Mb : ℤ, Ma * ((c : ℤ) + a - b) = k * (2 * b + a - 2 * c) ∧
        Mb * ((c : ℤ) + b - a) = k * (2 * b + a + 2 * c) ∧
        (2 : ℤ) ∣ Ma - N ∧ (2 : ℤ) ∣ Mb - N)
    ↔ ∃ m : ℕ, 0 < m ∧ N = m ^ 2 * b * (a + 2 * b) := by
  have hc0 : (0 : ℤ) < (c : ℤ) := by exact_mod_cast pos_c a b c ha hb hc
  have hcZ : (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + a * b + b ^ 2 := by exact_mod_cast hc
  have hcopZ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  constructor
  · rintro ⟨k, hk, harea, Ma, Mb, hMa, hMb, hpa, hpb⟩
    have hA : (Ma + 2 * k) * ((c : ℤ) + a - b) = 3 * a * k := by linear_combination hMa
    have hB : (Mb - 2 * k) * ((c : ℤ) + b - a) = 3 * a * k := by linear_combination hMb
    have hpar : (2 : ℤ) ∣ (Ma + 2 * k) - (Mb - 2 * k) := by
      have : (Ma + 2 * k) - (Mb - 2 * k) = (Ma - N) - (Mb - N) + 4 * k := by ring
      rw [this]; exact dvd_add (dvd_sub hpa hpb) ⟨2 * k, by ring⟩
    obtain ⟨j, hj⟩ := b_dvd_k a b c k _ _ (by exact_mod_cast ha) (by exact_mod_cast hb) hc0 hcopZ
      hcZ hA hB hpar
    obtain ⟨m, hm, rfl⟩ := nat_scale b k hb hk j hj
    refine ⟨m, hm, ?_⟩
    have : N * b = (m ^ 2 * b * (a + 2 * b)) * b := by rw [harea]; ring
    exact Nat.eq_of_mul_eq_mul_right hb this
  · rintro ⟨m, hm, rfl⟩
    refine ⟨b * m, by positivity, by ring, ((c : ℤ) - a - b) * m, ((c : ℤ) + a + b) * m, ?_, ?_, ?_, ?_⟩
    · push_cast; linear_combination (m : ℤ) * hcZ
    · push_cast; linear_combination (m : ℤ) * hcZ
    · have hcp := Erdos634.SpectrumZhang.c_parity (a : ℤ) b c hcZ
      push_cast at hcp
      rw [two_dvd_iff]; push_cast; exact parity_alpha_a _ _ _ _ hcp
    · have hcp := Erdos634.SpectrumZhang.c_parity (a : ℤ) b c hcZ
      push_cast at hcp
      rw [two_dvd_iff]; push_cast; exact parity_alpha_b _ _ _ _ hcp

/-- **`thm:spectrum`, base-`β` clause** ("Symmetrically"): the mirror `a ↔ b`.  Spelled out, the
conditions are `N a = k²(2a+b)`, `M_β' = k(2a+b-2c)/(c+b-a)`, `M_α' = k(2a+b+2c)/(c+a-b)`. -/
theorem spectrum_beta_iff (a b c N : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (∃ k : ℕ, 0 < k ∧ N * a = k ^ 2 * (b + 2 * a) ∧
      ∃ Ma Mb : ℤ, Ma * ((c : ℤ) + b - a) = k * (2 * a + b - 2 * c) ∧
        Mb * ((c : ℤ) + a - b) = k * (2 * a + b + 2 * c) ∧
        (2 : ℤ) ∣ Ma - N ∧ (2 : ℤ) ∣ Mb - N)
    ↔ ∃ m : ℕ, 0 < m ∧ N = m ^ 2 * a * (2 * a + b) := by
  have := spectrum_alpha_iff b a c N hb ha hcop.symm (by rw [hc]; ring)
  refine this.trans (exists_congr fun m => ?_)
  constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by rw [h2]; ring⟩

/-- **`thm:spectrum`, `F₁` clause.**  Area equation `N b = k²(a+b)`, `M_α = 3ak/X - k`,
`M_β = 3ak/Y + k` (`X = c+a-b`, `Y = c+b-a`), i.e. `M_α X = k(2a+b-c)`, `M_β Y = k(2a+b+c)`;
admissible counts are exactly `N = m² b (a+b)`. -/
theorem spectrum_F1_iff (a b c N : ℕ) (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) :
    (∃ k : ℕ, 0 < k ∧ N * b = k ^ 2 * (a + b) ∧
      ∃ Ma Mb : ℤ, Ma * ((c : ℤ) + a - b) = k * (2 * a + b - c) ∧
        Mb * ((c : ℤ) + b - a) = k * (2 * a + b + c) ∧
        (2 : ℤ) ∣ Ma - N ∧ (2 : ℤ) ∣ Mb - N)
    ↔ ∃ m : ℕ, 0 < m ∧ N = m ^ 2 * b * (a + b) := by
  have hc0 : (0 : ℤ) < (c : ℤ) := by exact_mod_cast pos_c a b c ha hb hc
  have hcZ : (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + a * b + b ^ 2 := by exact_mod_cast hc
  have hcopZ : IsCoprime (a : ℤ) (b : ℤ) := Nat.isCoprime_iff_coprime.mpr hcop
  constructor
  · rintro ⟨k, hk, harea, Ma, Mb, hMa, hMb, hpa, hpb⟩
    have hA : (Ma + k) * ((c : ℤ) + a - b) = 3 * a * k := by linear_combination hMa
    have hB : (Mb - k) * ((c : ℤ) + b - a) = 3 * a * k := by linear_combination hMb
    have hpar : (2 : ℤ) ∣ (Ma + k) - (Mb - k) := by
      have : (Ma + k) - (Mb - k) = (Ma - N) - (Mb - N) + 2 * k := by ring
      rw [this]; exact dvd_add (dvd_sub hpa hpb) ⟨k, by ring⟩
    obtain ⟨j, hj⟩ := b_dvd_k a b c k _ _ (by exact_mod_cast ha) (by exact_mod_cast hb) hc0 hcopZ
      hcZ hA hB hpar
    obtain ⟨m, hm, rfl⟩ := nat_scale b k hb hk j hj
    refine ⟨m, hm, ?_⟩
    have : N * b = (m ^ 2 * b * (a + b)) * b := by rw [harea]; ring
    exact Nat.eq_of_mul_eq_mul_right hb this
  · rintro ⟨m, hm, rfl⟩
    refine ⟨b * m, by positivity, by ring, ((c : ℤ) - a) * m, ((c : ℤ) + a) * m, ?_, ?_, ?_, ?_⟩
    · push_cast; linear_combination (m : ℤ) * hcZ
    · push_cast; linear_combination (m : ℤ) * hcZ
    · have hcp := Erdos634.SpectrumZhang.c_parity (a : ℤ) b c hcZ
      push_cast at hcp
      rw [two_dvd_iff]; push_cast; exact parity_F1a _ _ _ _ hcp
    · have hcp := Erdos634.SpectrumZhang.c_parity (a : ℤ) b c hcZ
      push_cast at hcp
      rw [two_dvd_iff]; push_cast; exact parity_F1b _ _ _ _ hcp

/-! ## `thm:admissible`, arithmetic half -/

/-- **`thm:admissible` (arithmetic half).**  `(a,b,c)` primitive `120°`-triple, `b = d e²`, `d`
squarefree.  If `N b = k²(a+2b)` (area equation) and the base-`α` invariant value `M = k(c-a-b)/b`
is an integer (`M b = k (c-a-b)`) with `M ≡ N (mod 2)` -- both supplied by `cor:int` for a real
tiling -- then `k = d e w` for a positive `w`, `N = d w² (a+2b)`, `e ∣ w(c-a-b)` and
`w(c-a-b)/e = M ≡ N (mod 2)`. -/
theorem admissible_arith (a b c d e N k : ℕ) (hb : 0 < b) (hcop : Nat.Coprime a b)
    (hbde : b = d * e ^ 2) (hd : Squarefree d) (hk : 0 < k)
    (harea : N * b = k ^ 2 * (a + 2 * b))
    (M : ℤ) (hM : M * b = k * ((c : ℤ) - a - b)) (hpar : (2 : ℤ) ∣ M - N) :
    ∃ w : ℕ, 0 < w ∧ k = d * e * w ∧ N = d * w ^ 2 * (a + 2 * b) ∧
      (e : ℤ) ∣ w * ((c : ℤ) - a - b) ∧ (w * ((c : ℤ) - a - b)) / (e : ℤ) = M ∧
      (2 : ℤ) ∣ (w * ((c : ℤ) - a - b)) / (e : ℤ) - N := by
  have hcb : Nat.Coprime b (a + 2 * b) := (Nat.coprime_add_mul_right_right b a 2).mpr hcop.symm
  have hbk2 : b ∣ k ^ 2 := by
    have : b ∣ k ^ 2 * (a + 2 * b) := ⟨N, by rw [← harea]; ring⟩
    exact hcb.dvd_of_dvd_mul_right this
  obtain ⟨w, hw⟩ := Erdos634.AdmissibleSpectrum.sqfree_scale_dvd hbde hd hk.ne' hbk2
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h | h
    · subst h; simp at hw; omega
    · exact h
  have hN : N = d * w ^ 2 * (a + 2 * b) :=
    Erdos634.AdmissibleSpectrum.count_eq N a b d e w hbde hb (by rw [← hw]; exact harea)
  have hd0 : d ≠ 0 := hd.ne_zero
  have he0 : e ≠ 0 := by rintro rfl; simp at hbde; omega
  have hMe : M * e = w * ((c : ℤ) - a - b) := by
    have hde : (d : ℤ) * e ≠ 0 := by positivity
    have h1 : (d : ℤ) * e * (M * e) = (d : ℤ) * e * (w * ((c : ℤ) - a - b)) := by
      have hkZ : (k : ℤ) = d * e * w := by exact_mod_cast hw
      have hbZ : (b : ℤ) = d * e ^ 2 := by exact_mod_cast hbde
      linear_combination hM - M * hbZ + ((c : ℤ) - a - b) * hkZ
    exact mul_left_cancel₀ hde h1
  have hq : (w * ((c : ℤ) - a - b)) / (e : ℤ) = M := by
    rw [← hMe]; exact Int.mul_ediv_cancel M (by exact_mod_cast he0)
  refine ⟨w, hwpos, hw, hN, ⟨M, by rw [← hMe]; ring⟩, hq, by rw [hq]; exact hpar⟩

/-! ## `thm:lattice`, paper form -/

theorem zmod2_two : (2 : ZMod 2) = 0 := by decide

/-- Translate the natural-number divisibility/parity clauses of `SpectrumLattice` (for `r₀ = -r ≥ 0`)
into the paper's integer clauses `e ∣ w r`, `w r / e ≡ N (mod 2)` with `r = -r₀`. -/
theorem conv_lemma (e rn w N : ℕ) (he : 0 < e) :
    (e ∣ w * rn ∧ ((w * rn / e : ℕ) : ZMod 2) = (N : ZMod 2)) ↔
    ((e : ℤ) ∣ (w : ℤ) * (-(rn : ℤ)) ∧ (2 : ℤ) ∣ ((w : ℤ) * (-(rn : ℤ))) / (e : ℤ) - (N : ℤ)) := by
  have he0 : (e : ℤ) ≠ 0 := by exact_mod_cast he.ne'
  constructor
  · rintro ⟨⟨x, hx⟩, hp⟩
    have hdiv : w * rn / e = x := by rw [hx]; exact Nat.mul_div_cancel_left x he
    rw [hdiv] at hp
    have hz : (w : ℤ) * (-(rn : ℤ)) = (e : ℤ) * (-(x : ℤ)) := by
      have : ((w * rn : ℕ) : ℤ) = ((e * x : ℕ) : ℤ) := by rw [hx]
      push_cast at this; linarith
    refine ⟨⟨-(x : ℤ), hz⟩, ?_⟩
    rw [hz, Int.mul_ediv_cancel_left _ he0, two_dvd_iff]
    push_cast
    linear_combination (-1 : ZMod 2) * hp - (N : ZMod 2) * zmod2_two
  · rintro ⟨⟨q, hq⟩, hp⟩
    have hnn : 0 ≤ -q := by
      have h1 : (0 : ℤ) ≤ (w : ℤ) * (rn : ℤ) := by positivity
      have h2 : (e : ℤ) * (-q) = (w : ℤ) * (rn : ℤ) := by linarith
      by_contra hneg; push Not at hneg
      have : (e : ℤ) * (-q) < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast he) hneg
      linarith
    obtain ⟨x, hxq⟩ : ∃ x : ℕ, (x : ℤ) = -q := ⟨(-q).toNat, Int.toNat_of_nonneg hnn⟩
    have hwx : w * rn = e * x := by
      have : ((w * rn : ℕ) : ℤ) = ((e * x : ℕ) : ℤ) := by push_cast; rw [hxq]; linarith
      exact_mod_cast this
    have hdiv : w * rn / e = x := by rw [hwx]; exact Nat.mul_div_cancel_left x he
    refine ⟨⟨x, hwx⟩, ?_⟩
    rw [hdiv]
    rw [hq, Int.mul_ediv_cancel_left _ he0, two_dvd_iff] at hp
    push_cast at hp
    have hxc : (x : ZMod 2) = -(q : ZMod 2) := by
      have := congrArg (fun z : ℤ => (z : ZMod 2)) hxq
      push_cast at this; exact this
    rw [hxc]
    linear_combination (-1 : ZMod 2) * hp - (N : ZMod 2) * zmod2_two

/-- `T`-parity condition: `2 ∣ -r₁ + d e₁²(a+2b)` iff `r₁ + d e₁²(a+2b) = 0` in `ZMod 2`. -/
theorem T_cond (r1 d e1 a2b : ℕ) :
    (2 : ℤ) ∣ (-(r1 : ℤ) + (d : ℤ) * (e1 : ℤ) ^ 2 * (a2b : ℤ)) ↔
      ((r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2 * (a2b : ZMod 2) = 0) := by
  rw [two_dvd_iff]; push_cast
  constructor
  · intro h; linear_combination h + (r1 : ZMod 2) * zmod2_two
  · intro h; linear_combination h - (r1 : ZMod 2) * zmod2_two

/-- **`thm:lattice`, in the paper's own notation.**  `(a,b,c)` a primitive `120°`-triple,
`b = d e²`, `r = c-a-b` (a negative integer), `g = gcd(e,r)`, `e₁ = e/g`,
`T = r/g + d e₁² (a+2b) (mod 2)`, `E = e₁` if `T` even else `2e₁`.  The counts
`N = d w²(a+2b)` with `w ≥ 1`, `e ∣ w r` and `w r / e ≡ N (mod 2)` (the conditions of
`thm:admissible`) are exactly `N = d (E u)² (a+2b)`, `u ≥ 1`. -/
theorem lattice_paper (a b c d e : ℕ) (ha : 0 < a) (hb0 : 0 < b) (hcop : Nat.Coprime a b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hbde : b = d * e ^ 2) (he : 0 < e) :
    {N : ℕ | ∃ w : ℕ, 0 < w ∧ N = d * w ^ 2 * (a + 2 * b) ∧
        (e : ℤ) ∣ w * ((c : ℤ) - a - b) ∧
        (2 : ℤ) ∣ (w * ((c : ℤ) - a - b)) / (e : ℤ) - N}
    = {N : ℕ | ∃ u : ℕ, 0 < u ∧ N = d * ((if (2 : ℤ) ∣ ((c : ℤ) - a - b) / ((Int.gcd e ((c : ℤ) - a - b) : ℕ) : ℤ)
          + d * ((e / Int.gcd e ((c : ℤ) - a - b) : ℕ) : ℤ) ^ 2 * (a + 2 * b)
        then e / Int.gcd e ((c : ℤ) - a - b) else 2 * (e / Int.gcd e ((c : ℤ) - a - b))) * u) ^ 2
        * (a + 2 * b)} := by
  have hclt : c < a + b := by
    by_contra h; push Not at h
    have := Nat.mul_pos ha hb0
    nlinarith
  obtain ⟨rn, hrn⟩ : ∃ rn, rn = a + b - c := ⟨_, rfl⟩
  have hr : (c : ℤ) - a - b = -(rn : ℤ) := by omega
  have hg : Int.gcd (e : ℤ) (-(rn : ℤ)) = Nat.gcd e rn := by
    simp [Int.gcd, Int.natAbs_neg]
  rw [hr, hg]
  obtain ⟨g, hgdef⟩ : ∃ g, g = Nat.gcd e rn := ⟨_, rfl⟩
  rw [← hgdef]
  have hgpos : 0 < g := by rw [hgdef]; exact Nat.gcd_pos_of_pos_left _ he
  obtain ⟨e1, he1def⟩ : ∃ e1, e1 = e / g := ⟨_, rfl⟩
  obtain ⟨r1, hr1def⟩ : ∃ r1, r1 = rn / g := ⟨_, rfl⟩
  rw [← he1def]
  have he_eq : e = g * e1 := by rw [he1def, hgdef]; exact (Nat.mul_div_cancel' (Nat.gcd_dvd_left e rn)).symm
  have hr_eq : rn = g * r1 := by rw [hr1def, hgdef]; exact (Nat.mul_div_cancel' (Nat.gcd_dvd_right e rn)).symm
  have hcop' : Nat.Coprime e1 r1 := by
    rw [he1def, hr1def, hgdef]; exact Nat.coprime_div_gcd_div_gcd (by rw [← hgdef]; exact hgpos)
  have he1pos : 0 < e1 := by
    rcases Nat.eq_zero_or_pos e1 with h | h
    · rw [h] at he_eq; omega
    · exact h
  have hdiv : (-(rn : ℤ)) / (g : ℤ) = -(r1 : ℤ) := by
    have : -((rn : ℕ) : ℤ) = (g : ℤ) * (-(r1 : ℤ)) := by rw [hr_eq]; push_cast; ring
    rw [this, Int.mul_ediv_cancel_left _ (by exact_mod_cast hgpos.ne')]
  rw [hdiv]
  have hset := Erdos634.SpectrumLattice.admissible_set_eq e rn d (a + 2 * b) g e1 r1 hgpos he1pos
    he_eq hr_eq hcop'
  have hTc := T_cond r1 d e1 (a + 2 * b)
  ext N
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨w, hw, rfl, hdvd, hpar⟩
    have hconv := (conv_lemma e rn w (d * w ^ 2 * (a + 2 * b)) he).mpr ⟨hdvd, hpar⟩
    have hmem : w ∈ {w : ℕ | 0 < w ∧ e ∣ w * rn ∧
        ((w * rn / e : ℕ) : ZMod 2) = (d : ZMod 2) * (w : ZMod 2) ^ 2 * ((a + 2 * b : ℕ) : ZMod 2)} := by
      refine ⟨hw, hconv.1, ?_⟩
      rw [hconv.2]; push_cast; ring
    rw [hset] at hmem
    obtain ⟨u, hu, hwu⟩ := hmem
    refine ⟨u, hu, ?_⟩
    by_cases hT : (2 : ℤ) ∣ -(r1 : ℤ) + (d : ℤ) * (e1 : ℤ) ^ 2 * ((a + 2 * b : ℕ) : ℤ)
    · rw [if_pos (by push_cast at hT ⊢; exact hT)]
      rw [if_pos (hTc.mp hT)] at hwu
      rw [← hwu]
    · rw [if_neg (by push_cast at hT ⊢; exact hT)]
      rw [if_neg (fun h => hT (hTc.mpr h))] at hwu
      rw [← hwu]
  · rintro ⟨u, hu, rfl⟩
    by_cases hT : (2 : ℤ) ∣ -(r1 : ℤ) + (d : ℤ) * (e1 : ℤ) ^ 2 * ((a + 2 * b : ℕ) : ℤ)
    · rw [if_pos (by push_cast at hT ⊢; exact hT)]
      have hmem : e1 * u ∈ {w : ℕ | ∃ u : ℕ, 0 < u ∧ w = (if (r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2
          * ((a + 2 * b : ℕ) : ZMod 2) = 0 then e1 else 2 * e1) * u} :=
        ⟨u, hu, by rw [if_pos (hTc.mp hT)]⟩
      rw [← hset] at hmem
      obtain ⟨hw, hd1, hp1⟩ := hmem
      have hconv := (conv_lemma e rn (e1 * u) (d * (e1 * u) ^ 2 * (a + 2 * b)) he).mp
        ⟨hd1, by rw [hp1]; push_cast; ring⟩
      exact ⟨e1 * u, hw, rfl, hconv.1, hconv.2⟩
    · rw [if_neg (by push_cast at hT ⊢; exact hT)]
      have hmem : 2 * e1 * u ∈ {w : ℕ | ∃ u : ℕ, 0 < u ∧ w = (if (r1 : ZMod 2) + (d : ZMod 2) * (e1 : ZMod 2) ^ 2
          * ((a + 2 * b : ℕ) : ZMod 2) = 0 then e1 else 2 * e1) * u} :=
        ⟨u, hu, by rw [if_neg (fun h => hT (hTc.mpr h))]⟩
      rw [← hset] at hmem
      obtain ⟨hw, hd1, hp1⟩ := hmem
      have hconv := (conv_lemma e rn (2 * e1 * u) (d * (2 * e1 * u) ^ 2 * (a + 2 * b)) he).mp
        ⟨hd1, by rw [hp1]; push_cast; ring⟩
      exact ⟨2 * e1 * u, hw, rfl, hconv.1, hconv.2⟩

/-! ## Non-vacuity and a control instance -/

/-- `(3,5,7)`, `N = 65 = 1²·5·13` is spectrum-admissible (the paper's `65 = b(a+2b)`). -/
theorem witness_65 : ∃ k : ℕ, 0 < k ∧ 65 * 5 = k ^ 2 * (3 + 2 * 5) ∧
      ∃ Ma Mb : ℤ, Ma * ((7 : ℕ) + (3 : ℕ) - (5 : ℕ)) = k * (2 * (5 : ℕ) + (3 : ℕ) - 2 * (7 : ℕ)) ∧
        Mb * ((7 : ℕ) + (5 : ℕ) - (3 : ℕ)) = k * (2 * (5 : ℕ) + (3 : ℕ) + 2 * (7 : ℕ)) ∧
        (2 : ℤ) ∣ Ma - (65 : ℕ) ∧ (2 : ℤ) ∣ Mb - (65 : ℕ) :=
  (spectrum_alpha_iff 3 5 7 65 (by norm_num) (by norm_num) (by norm_num) (by norm_num)).mpr
    ⟨1, by norm_num, by norm_num⟩

/-- **Control instance.**  On `(11,24,31)` the single-invariant lattice of
`thm:lattice` contains `N = 354 = 6·1²·59` (`w = 1`: `e = 2 ∣ w r = -4`, quotient `-2 ≡ 354`), but the
full spectrum condition excludes it (`354 ≠ m²·24·59`).  So the converse is not vacuous. -/
theorem control_354 :
    (∃ w : ℕ, 0 < w ∧ (354 : ℕ) = 6 * w ^ 2 * (11 + 2 * 24) ∧
        ((2 : ℕ) : ℤ) ∣ w * (((31 : ℕ) : ℤ) - (11 : ℕ) - (24 : ℕ)) ∧
        (2 : ℤ) ∣ (w * (((31 : ℕ) : ℤ) - (11 : ℕ) - (24 : ℕ))) / ((2 : ℕ) : ℤ) - (354 : ℕ))
    ∧ ¬ (∃ k : ℕ, 0 < k ∧ 354 * 24 = k ^ 2 * (11 + 2 * 24) ∧
      ∃ Ma Mb : ℤ, Ma * (((31 : ℕ) : ℤ) + (11 : ℕ) - (24 : ℕ)) = k * (2 * (24 : ℕ) + (11 : ℕ) - 2 * (31 : ℕ)) ∧
        Mb * (((31 : ℕ) : ℤ) + (24 : ℕ) - (11 : ℕ)) = k * (2 * (24 : ℕ) + (11 : ℕ) + 2 * (31 : ℕ)) ∧
        (2 : ℤ) ∣ Ma - (354 : ℕ) ∧ (2 : ℤ) ∣ Mb - (354 : ℕ)) := by
  refine ⟨⟨1, by norm_num, by norm_num, by norm_num, by norm_num⟩, ?_⟩
  rw [spectrum_alpha_iff 11 24 31 354 (by norm_num) (by norm_num) (by norm_num) (by norm_num)]
  rintro ⟨m, hm, h⟩
  have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ hm
  nlinarith

/-- Every positive `b` is `d e²` with `d` squarefree and `e ≥ 1` (the paper's "write `b = de²`"). -/
theorem sqfree_decomp (b : ℕ) (hb : 0 < b) : ∃ d e : ℕ, 0 < e ∧ b = d * e ^ 2 ∧ Squarefree d := by
  obtain ⟨d, e, h, hd⟩ := Nat.sq_mul_squarefree b
  refine ⟨d, e, ?_, by rw [← h]; ring, hd⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp at h; omega
  · exact he

end Erdos634.Draft.FDDSpectrum

#print axioms Erdos634.Draft.FDDSpectrum.sqfree_decomp
#print axioms Erdos634.Draft.FDDSpectrum.b_dvd_k
#print axioms Erdos634.Draft.FDDSpectrum.spectrum_alpha_iff
#print axioms Erdos634.Draft.FDDSpectrum.spectrum_beta_iff
#print axioms Erdos634.Draft.FDDSpectrum.spectrum_F1_iff
#print axioms Erdos634.Draft.FDDSpectrum.admissible_arith
#print axioms Erdos634.Draft.FDDSpectrum.lattice_paper
#print axioms Erdos634.Draft.FDDSpectrum.witness_65
#print axioms Erdos634.Draft.FDDSpectrum.control_354
