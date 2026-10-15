-- ThickEFminus1Probe.lean — Arithmetic/metric core of proof_S2 (e = f−1, f ≥ 3, m = 1 base-β).
-- Steps (4)–(7): V-distance identity, corners below base, b < a, leftover non-representability.
-- In Erdos634.All. Part (B), the geometric glue, is in Draft/ThickEFminus1Glue.lean (not in All).
-- Nothing in this file depends on that file.
--
-- Conventions: tile (a,b,c) = (ef, f²−e², f²); sin(α/2) = e/(2f); apex at origin, axis downward.

import Mathlib

namespace Erdos634.ThickEFminus1Probe

open Real

/-! ## Step (4): the V-distance identity -/

/-- `a + c = f·b` holds exactly when `e = f − 1` (for `e, f > 0`). -/
theorem a_add_c_eq_fb_iff {e f : ℝ} (he : 0 < e) (hf : 0 < f) :
    e * f + f ^ 2 = f * (f ^ 2 - e ^ 2) ↔ e = f - 1 := by
  constructor
  · intro h
    have h1 : f * ((e + f) * (f - e - 1)) = 0 := by linear_combination -h
    rcases mul_eq_zero.mp h1 with h2 | h2
    · linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · linarith
    · linarith
  · rintro rfl; ring

/-- The mismatch ray `r` (angle `α/2` from the axis) meets the base at distance `f·b`:
`f³·cos(3α/2) = f(f²−e²)·cos(α/2)` when `sin(α/2) = e/(2f)`. -/
theorem base_depth_along_ray {e f x : ℝ} (hf : f ≠ 0) (hs : sin x = e / (2 * f)) :
    f ^ 3 * cos (3 * x) = f * (f ^ 2 - e ^ 2) * cos x := by
  rw [cos_three_mul]
  have hc : cos x ^ 2 = 1 - e ^ 2 / (4 * f ^ 2) := by
    rw [cos_sq', hs]; field_simp; ring
  have : f ^ 3 * (4 * cos x ^ 3 - 3 * cos x) = f ^ 3 * cos x * (4 * cos x ^ 2 - 3) := by ring
  rw [this, hc]; field_simp; ring

/-- **Step (4).** At `e = f−1`, `V` (at distance `c = f²` along `r`) is at vertical depth exactly
`a·cos(α/2)` above the base (base at depth `f³·cos(3α/2)`). -/
theorem V_depth_above_base {f x : ℝ} (hf : f ≠ 0) (hs : sin x = (f - 1) / (2 * f)) :
    f ^ 3 * cos (3 * x) - f ^ 2 * cos x = ((f - 1) * f) * cos x := by
  rw [base_depth_along_ray hf hs]; ring

/-! ## Step (5): corners against ρ put a vertex below the base -/

/-- **Step (5), α-corner, `b` along ρ.** The `c`-flank points at angle `α/2` on the other side of the
axis; its drop `c·cos(α/2)` exceeds `V`'s height `a·cos(α/2)`. -/
theorem alpha_corner_below {a c α : ℝ} (hac : a < c) (hα0 : 0 < α) (hαπ : α < π) :
    a * cos (α / 2) < c * cos (-(α / 2) ) := by
  rw [cos_neg]
  have : 0 < cos (α / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  nlinarith

/-- **Step (5), β-corner, `a` along ρ.** The `c`-flank points at angle `α/2 − β` from the axis, with
`0 < β < α`, so it drops `c·cos(α/2−β) > a·cos(α/2)`. -/
theorem beta_corner_below {a c α β : ℝ} (ha : 0 < a) (hac : a < c) (hβ0 : 0 < β) (hβα : β < α)
    (hαπ : α < π) :
    a * cos (α / 2) < c * cos (α / 2 - β) := by
  have hpos : 0 < cos (α / 2) := cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hlt : cos (α / 2) < cos (α / 2 - β) := by
    rw [← cos_abs (α / 2 - β)]
    apply cos_lt_cos_of_nonneg_of_le_pi_div_two (abs_nonneg _) (by linarith)
    rw [abs_lt]; constructor <;> linarith
  nlinarith

/-- `b < a` for the thick tile at every real `f > (3+√5)/2`, in particular every integer `f ≥ 3`. -/
theorem b_lt_a {f : ℝ} (hf : 3 ≤ f) : 2 * f - 1 < f ^ 2 - f := by nlinarith

/-! ## Step (7): the leftover `a − b` is not a sum of sides -/

/-- **Step (7).** For integer `f ≥ 3`, no `na·a + nb·b + nc·c` equals `a − b`, where
`(a,b,c) = (f²−f, 2f−1, f²)`; stated additively as `… + b ≠ a`. -/
theorem leftover_a_sub_b_nonrep (f na nb nc : ℕ) (hf : 3 ≤ f) :
    na * (f ^ 2 - f) + nb * (2 * f - 1) + nc * f ^ 2 + (2 * f - 1) ≠ f ^ 2 - f := by
  intro h
  have hff : f ≤ f ^ 2 := by nlinarith
  obtain ⟨A, hA⟩ : ∃ A, A + f = f ^ 2 := ⟨f ^ 2 - f, by omega⟩
  obtain ⟨B, hB⟩ : ∃ B, B + 1 = 2 * f := ⟨2 * f - 1, by omega⟩
  have hAe : f ^ 2 - f = A := by omega
  have hBe : 2 * f - 1 = B := by omega
  rw [hAe, hBe] at h
  have hB5 : 5 ≤ B := by omega
  have hna : na = 0 := by
    rcases Nat.eq_zero_or_pos na with h0 | h0
    · exact h0
    · exfalso; nlinarith
  have hnc : nc = 0 := by
    rcases Nat.eq_zero_or_pos nc with h0 | h0
    · exact h0
    · exfalso; nlinarith
  subst hna hnc
  -- (nb+1)·B = A, and 4A = B² − 1.
  have h4 : 4 * A + 1 = B ^ 2 := by nlinarith
  have hk : (nb + 1) * B = A := by linarith
  have hz : (B : ℤ) * (B - 4 * (nb + 1)) = 1 := by
    have : (4 * ((nb + 1) * B) + 1 : ℤ) = (B : ℤ) ^ 2 := by exact_mod_cast (hk ▸ h4)
    linear_combination -this
  have hB5' : (5 : ℤ) ≤ B := by exact_mod_cast hB5
  rcases le_or_gt ((B : ℤ) - 4 * (nb + 1)) 0 with h1 | h1
  · nlinarith
  · nlinarith

/-- Step (6) is already in the corpus: `ApexRigidity.two_gamma` (`2γ = π + α`). Step (3)'s case
split is `BaseBetaWalks.pierced_corner_types`. Re-derived here only as the angle fact used. -/
theorem two_gamma_gt_pi {α β γ : ℝ} (hsum : 3 * α + 2 * β = π) (hγ : γ = 2 * α + β) (hα : 0 < α) :
    π < 2 * γ := by subst hγ; linarith

end Erdos634.ThickEFminus1Probe

#print axioms Erdos634.ThickEFminus1Probe.a_add_c_eq_fb_iff
#print axioms Erdos634.ThickEFminus1Probe.base_depth_along_ray
#print axioms Erdos634.ThickEFminus1Probe.V_depth_above_base
#print axioms Erdos634.ThickEFminus1Probe.alpha_corner_below
#print axioms Erdos634.ThickEFminus1Probe.beta_corner_below
#print axioms Erdos634.ThickEFminus1Probe.b_lt_a
#print axioms Erdos634.ThickEFminus1Probe.leftover_a_sub_b_nonrep
#print axioms Erdos634.ThickEFminus1Probe.two_gamma_gt_pi
