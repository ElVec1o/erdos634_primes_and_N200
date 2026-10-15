-- Draft/FluxDRem45.lean: the remark on base-α at `p ≡ 3 (mod 4)`, arithmetic core only.  Imported by
-- `All`.
--
-- Statement formalized: for coprime `1 ≤ e < f` (rational tile `(ef, f²−e², f²)`) and a prime `p` with
-- the scaling equation `p·(f² − e²) = k²·(2f² − e²)`: `gcd(2f²−e², f²−e²) = 1`, so
-- `(2f² − e²) ∣ p`, hence `2f² − e² = p`, `k² = f² − e²`, `p = f² + k²`, and `p ≢ 3 (mod 4)`.
--
-- Not formalized: the geometric derivation of the scaling equation (the target is
-- `k·(f², f², 2f²−e²)`).  The conclusion is that of the iso-α prime case, whose arithmetic is in
-- Lean for every prime (`IsoAlpha.isoalpha_not_prime`, from a different equation); this file gives
-- the remark's own route.  Witness: `rem45_witness` / `rem45_applied`:
-- `(e, f, k, p) = (3, 5, 4, 41)` meets every hypothesis (`41·16 = 16·41`, 41 prime, gcd(3,5) = 1),
-- and the conclusion `41 = 5² + 4² ≢ 3 (mod 4)` is reached through the theorem.  This is an
-- arithmetic instance only; no tiling is claimed.
import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.Coprime.Lemmas

namespace Erdos634.Geometry

/-- **Remark 4.5, arithmetic core.** -/
theorem Rem45.not_three_mod_four {e f k p : ℕ} (he : 1 ≤ e) (hef : e < f)
    (hcop : Nat.Coprime e f) (hp : p.Prime)
    (h : (p : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) = (k : ℤ) ^ 2 * (2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2)) :
    p = f ^ 2 + k ^ 2 ∧ p % 4 ≠ 3 := by
  -- `gcd(2f² − e², f² − e²) = 1`
  obtain ⟨x, y, hxy⟩ : IsCoprime ((e : ℤ) ^ 2) ((f : ℤ) ^ 2) :=
    (Nat.isCoprime_iff_coprime.mpr hcop).pow
  have hAB : IsCoprime (2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) :=
    ⟨x + y, -2 * x - y, by linear_combination hxy⟩
  have hdvd : (2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) ∣ (p : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) :=
    ⟨(k : ℤ) ^ 2, by rw [h]; ring⟩
  have hAp : (2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) ∣ (p : ℤ) := hAB.dvd_of_dvd_mul_right hdvd
  -- `2f² − e² > 1`, so it is `p`
  have he' : (1 : ℤ) ≤ e := by exact_mod_cast he
  have hef' : (e : ℤ) < f := by exact_mod_cast hef
  have hf2 : (2 : ℤ) ≤ f := by omega
  have hA1 : 1 < 2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have h1 : (0 : ℤ) < ((f : ℤ) - e) * (f + e) := mul_pos (by linarith) (by linarith)
    have h2 : (2 : ℤ) * 2 ≤ (f : ℤ) * f := mul_le_mul hf2 hf2 (by norm_num) (by linarith)
    nlinarith
  have hAeq : 2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2 = p := by
    obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le (by linarith : (0 : ℤ) ≤ 2 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2)
    rw [hn] at hAp hA1 ⊢
    have hnp : n ∣ p := by exact_mod_cast hAp
    rcases (Nat.dvd_prime hp).mp hnp with h1 | h1
    · exfalso; rw [h1] at hA1; norm_num at hA1
    · rw [h1]
  -- `k² = f² − e²`, `p = f² + k²`
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hk : (k : ℤ) ^ 2 = (f : ℤ) ^ 2 - (e : ℤ) ^ 2 := by
    have : (p : ℤ) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2 - (k : ℤ) ^ 2) = 0 := by
      rw [← hAeq] at h ⊢; linear_combination h
    have := (mul_eq_zero.mp this).resolve_left hp0
    linarith
  have hpz : (p : ℤ) = (f : ℤ) ^ 2 + (k : ℤ) ^ 2 := by rw [← hAeq, hk]; ring
  have hpn : p = f ^ 2 + k ^ 2 := by exact_mod_cast hpz
  refine ⟨hpn, fun h3 => ?_⟩
  -- a sum of two squares is never `3 (mod 4)`
  have key : ∀ x y : ZMod 4, x ^ 2 + y ^ 2 ≠ 3 := by decide
  apply key (f : ZMod 4) (k : ZMod 4)
  have h4 : ((p : ℕ) : ZMod 4) = 3 := by rw [← ZMod.natCast_mod, h3]; decide
  have h5 := (congrArg (Nat.cast : ℕ → ZMod 4) hpn).symm.trans h4
  push_cast at h5
  exact h5

/-- **Every hypothesis of `Rem45.not_three_mod_four` holds at `(e, f, k, p) = (3, 5, 4, 41)`.** -/
theorem rem45_witness : (41 : ℤ) * ((5 : ℤ) ^ 2 - (3 : ℤ) ^ 2) = (4 : ℤ) ^ 2 * (2 * (5 : ℤ) ^ 2 - (3 : ℤ) ^ 2)
    ∧ Nat.Prime 41 ∧ Nat.Coprime 3 5 ∧ (41 : ℕ) = 5 ^ 2 + 4 ^ 2 ∧ 41 % 4 ≠ 3 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- `Rem45.not_three_mod_four` applied to the `(e, f, k, p) = (3, 5, 4, 41)` instance. -/
theorem rem45_applied : (41 : ℕ) = 5 ^ 2 + 4 ^ 2 ∧ 41 % 4 ≠ 3 :=
  Rem45.not_three_mod_four (e := 3) (f := 5) (k := 4) (p := 41) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Rem45.not_three_mod_four
#print axioms Erdos634.Geometry.rem45_witness
#print axioms Erdos634.Geometry.rem45_applied
