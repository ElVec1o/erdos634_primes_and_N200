import Mathlib
import Erdos634.E1BaseWord
import Erdos634.FanKill

/-!
# The fan depth of the tile `(f, f²−1, f²)` as finite statements

The claims about a search program's tree (two fans, side cases, secondary chain, node counts,
measured fan depth) are not Lean statements and are not made here.

* `fan_depth_table` — for the tile `(f, f²−1, f²)` (`e = 1`), with `α` the angle opposite `f`
  (law of cosines, `0 ≤ α ≤ π`) and `β` defined by the `e = 1` relation `3α + 2β = π`:
  `⌊β/α⌋ = 4, 6, 7, 9, 11, 12, 14` at `f = 4, …, 10`.  Proved from `π`-bounds (`Real.pi_gt_d6`,
  `Real.pi_lt_d6`) and the Taylor bounds `Real.cos_bound`, `Real.one_sub_sq_div_two_le_cos`.
* `beta_div_alpha` — `β/α = π/(2α) − 3/2`.
* `fan_depth_table_witness` — the hypotheses are satisfiable at each `f` (`α = arccos (1 − 1/(2f²))`).
* `fanlaw_no_completion` — the `(4,2)`-seeded instance, and indeed every seed, has no completion at
  `f = 4, …, 10` (every `f ≥ 3`): an immediate corollary of `E1BaseWord.e1_family_f_ge_3_congruent`.

The termination arithmetic itself (`0 < β − kα < α` at `k = ⌊β/α⌋`, no exact fan) is
`FanKill.fan_remainder` / `FanKill.no_exact_fan`, general in `f`.

Standard axioms; no `sorry`.
-/

namespace Erdos634.Draft.HeurFanLaw

open Real

/-- The law-of-cosines value of the angle opposite `f` in the tile `(f, f²−1, f²)`. -/
noncomputable def cosAlpha (f : ℝ) : ℝ := ((f ^ 2 - 1) ^ 2 + (f ^ 2) ^ 2 - f ^ 2) / (2 * (f ^ 2 - 1) * f ^ 2)

theorem cosAlpha_eq {f : ℝ} (hf : 1 < f) : cosAlpha f = 1 - 1 / (2 * f ^ 2) := by
  unfold cosAlpha
  have h1 : f ^ 2 - 1 ≠ 0 := by nlinarith
  have h2 : f ^ 2 ≠ 0 := by positivity
  field_simp <;> ring

/-- `β/α = π/(2α) − 3/2` under the `e = 1` relation `3α + 2β = π`. -/
theorem beta_div_alpha {α β : ℝ} (hα : α ≠ 0) (hrel : 3 * α + 2 * β = π) :
    β / α = π / (2 * α) - 3 / 2 := by
  have hb : β = (π - 3 * α) / 2 := by linarith
  rw [hb]; field_simp <;> ring

/-- The floor from two angle bounds. -/
theorem floor_of_bounds {α β : ℝ} (k : ℕ) (hα : 0 < α) (hrel : 3 * α + 2 * β = π)
    (h1 : (2 * (k : ℝ) + 3) * α ≤ π) (h2 : π < (2 * (k : ℝ) + 5) * α) : ⌊β / α⌋₊ = k := by
  rw [Nat.floor_eq_iff]
  · constructor
    · rw [le_div_iff₀ hα]; linarith
    · rw [div_lt_iff₀ hα]; push_cast; linarith
  · have : 0 ≤ 2 * (k : ℝ) * α := by positivity
    apply div_nonneg _ hα.le; nlinarith

/-- The generic step: `⌊β/α⌋ = k` from `cos α = 1 − 1/(2f²)` and two numerical side conditions
on `n₁ = 2k+3`, `n₂ = 2k+5` (checked by `norm_num` per instance). -/
theorem fan_depth_of_cos (f : ℝ) (hf : 0 < f) (k : ℕ) {α β : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ π)
    (hcos : cos α = 1 - 1 / (2 * f ^ 2)) (hrel : 3 * α + 2 * β = π)
    (hU1 : (3.141593 : ℝ) / (2 * k + 3) ≤ 1)
    (hA : 1 / (2 * f ^ 2) <
      ((3.141592 : ℝ) / (2 * k + 3)) ^ 2 * (1 / 2 - 5 * ((3.141593 : ℝ) / (2 * k + 3)) ^ 2 / 96))
    (hB : ((3.141593 : ℝ) / (2 * k + 5)) ^ 2 < 1 / f ^ 2) :
    ⌊β / α⌋₊ = k := by
  have hpl := Real.pi_gt_d6
  have hpu := Real.pi_lt_d6
  have hn1 : (0 : ℝ) < 2 * k + 3 := by positivity
  have hn2 : (0 : ℝ) < 2 * k + 5 := by positivity
  -- upper bound on α
  have h1 : (2 * (k : ℝ) + 3) * α ≤ π := by
    by_contra hc
    push_neg at hc
    set x := π / (2 * k + 3) with hx
    have hxα : x < α := by rw [hx, div_lt_iff₀ hn1]; linarith
    have hx0 : 0 ≤ x := by positivity
    have hxL : (3.141592 : ℝ) / (2 * k + 3) ≤ x := by
      rw [hx]; exact div_le_div_of_nonneg_right hpl.le hn1.le
    have hxU : x ≤ (3.141593 : ℝ) / (2 * k + 3) := by
      rw [hx]; exact div_le_div_of_nonneg_right hpu.le hn1.le
    have hcl : cos α < cos x := Real.cos_lt_cos_of_nonneg_of_le_pi hx0 hπ hxα
    have hb := Real.cos_bound (x := x) (by rw [abs_of_nonneg hx0]; linarith)
    rw [abs_of_nonneg hx0] at hb
    have hb' := (abs_le.mp hb).2
    set L := (3.141592 : ℝ) / (2 * k + 3)
    set U := (3.141593 : ℝ) / (2 * k + 3)
    have hL0 : 0 ≤ L := by positivity
    have hs1 : L ^ 2 ≤ x ^ 2 := by nlinarith
    have hs2 : x ^ 2 ≤ U ^ 2 := by nlinarith
    have hx4 : x ^ 4 = x ^ 2 * x ^ 2 := by ring
    have hss : x ^ 2 * x ^ 2 ≤ x ^ 2 * U ^ 2 := mul_le_mul_of_nonneg_left hs2 (by positivity)
    have hcoef : 0 ≤ 1 / 2 - 5 * U ^ 2 / 96 := by
      have : U ^ 2 ≤ 1 := by nlinarith
      linarith
    have hprod : L ^ 2 * (1 / 2 - 5 * U ^ 2 / 96) ≤ x ^ 2 * (1 / 2 - 5 * U ^ 2 / 96) :=
      mul_le_mul_of_nonneg_right hs1 hcoef
    nlinarith
  -- lower bound on α
  have h2 : π < (2 * (k : ℝ) + 5) * α := by
    by_contra hc
    push_neg at hc
    set x := π / (2 * k + 5) with hx
    have hαx : α ≤ x := by rw [hx, le_div_iff₀ hn2]; linarith
    have hx0 : 0 ≤ x := by positivity
    have hxU : x ≤ (3.141593 : ℝ) / (2 * k + 5) := by
      rw [hx]; exact div_le_div_of_nonneg_right hpu.le hn2.le
    have hcl : cos x ≤ cos α := Real.cos_le_cos_of_nonneg_of_le_pi h0
      (by rw [hx]; exact div_le_self Real.pi_pos.le (by linarith)) hαx
    have hlb := Real.one_sub_sq_div_two_le_cos (x := x)
    have hs2 : x ^ 2 ≤ ((3.141593 : ℝ) / (2 * k + 5)) ^ 2 := by nlinarith
    have hf2 : 0 < f ^ 2 := by positivity
    have : 1 / (2 * f ^ 2) = (1 / f ^ 2) / 2 := by field_simp
    nlinarith
  have hα : 0 < α := by
    by_contra hc; push_neg at hc
    have : α = 0 := le_antisymm hc h0
    rw [this] at h2; simp at h2; linarith [Real.pi_pos]
  exact floor_of_bounds k hα hrel h1 h2

/-- The fan depths of the table, `f = 4, …, 10`. -/
def depth : ℕ → ℕ
  | 4 => 4 | 5 => 6 | 6 => 7 | 7 => 9 | 8 => 11 | 9 => 12 | 10 => 14 | _ => 0

/-- **The fan-depth table.**  For `f ∈ {4,…,10}`, `α ∈ [0, π]` the angle of the tile `(f, f²−1, f²)`
opposite `f` (law of cosines) and `β` given by `3α + 2β = π`:
`⌊β/α⌋ = 4, 6, 7, 9, 11, 12, 14` respectively. -/
theorem fan_depth_table (f : ℕ) (hf : f ∈ Finset.Icc 4 10) {α β : ℝ} (h0 : 0 ≤ α) (hπ : α ≤ π)
    (hcos : cos α = cosAlpha f) (hrel : 3 * α + 2 * β = π) : ⌊β / α⌋₊ = depth f := by
  have hf1 : (1 : ℝ) < f := by
    have := (Finset.mem_Icc.mp hf).1; exact_mod_cast (show 1 < f by omega)
  rw [cosAlpha_eq hf1] at hcos
  have hfpos : (0 : ℝ) < f := by linarith
  simp only [Finset.mem_Icc] at hf
  obtain ⟨hlo, hhi⟩ := hf
  interval_cases f <;> simp only [depth] <;>
    exact fan_depth_of_cos _ hfpos _ h0 hπ (by exact_mod_cast hcos) hrel
      (by norm_num) (by norm_num) (by norm_num)

/-- Non-vacuity: at each `f` of the table, `α = arccos(cosAlpha f)` and `β = (π − 3α)/2` meet
every hypothesis of `fan_depth_table`. -/
theorem fan_depth_table_witness (f : ℕ) (hf : f ∈ Finset.Icc 4 10) :
    ∃ α β : ℝ, 0 ≤ α ∧ α ≤ π ∧ cos α = cosAlpha f ∧ 3 * α + 2 * β = π ∧ ⌊β / α⌋₊ = depth f := by
  have hf1 : (1 : ℝ) < f := by
    have := (Finset.mem_Icc.mp hf).1; exact_mod_cast (show 1 < f by omega)
  have hc := cosAlpha_eq hf1
  have hf2 : 0 < (f : ℝ) ^ 2 := by positivity
  have hle1 : cosAlpha f ≤ 1 := by
    rw [hc]; have : 0 < 1 / (2 * (f : ℝ) ^ 2) := by positivity
    linarith
  have hge : -1 ≤ cosAlpha f := by
    rw [hc]; have : 1 / (2 * (f : ℝ) ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  refine ⟨arccos (cosAlpha f), (π - 3 * arccos (cosAlpha f)) / 2, arccos_nonneg _,
    arccos_le_pi _, cos_arccos hge hle1, by ring, ?_⟩
  exact fan_depth_table f hf (arccos_nonneg _) (arccos_le_pi _) (cos_arccos hge hle1) (by ring)

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose in
/-- **No completion** (corollary of `thm:e1family`): at every `f ≥ 3`, in particular `f = 4, …, 10`,
there is no congruent dissection of the `m = 1`, `e = 1` base-β target by the tile
`(f, f²−1, f²)`; a fortiori the `(4,2)`-seeded instance (any seed) has no completion. -/
theorem fanlaw_no_completion {N : ℕ} (D₀ : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega)))) :
    False :=
  Erdos634.E1BaseWord.e1_family_f_ge_3_congruent D₀ hn3 htgt hmod

end Erdos634.Draft.HeurFanLaw
