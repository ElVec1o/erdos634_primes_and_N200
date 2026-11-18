/-
Draft/WGapAngles.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P0.3).
Not imported by any aggregate.

Module W1a of the W-gap Lean plan (PROOF.md P12, "W1 WGapSectors", the arithmetic half): the angle ledger (F) of PROOF.md 0.3,
from the project's `AngleData α β γ` (`γ = 2α + β`, `3α + 2β = π`, `α/π` irrational).

* `ledger`   : for integers `x y z k`:  `x α + y β + z γ = k π  ↔  2x − 3y + z = 0 ∧ k = 2y − x`   (PROOF (0.2)).
* `ledger2`  : the two-sided form `x α + y β + z γ = x' α + y' β + z' γ + k π`  (PROOF 0.3, "more generally").
* `fill_*`   : the solution sets of the wedge fillings used in the hand proof, with natural-number multiplicities:
  straight angle `{α,β,γ} or {3α,2β}`; wedge `γ`: `γ` or `{2α, β}`; wedge `3α`; wedge `2α`; wedge `α`; wedge `β`; wedge `α+β`;
  wedge `π − β = 3α + β`: `{3α, β}` or `{α, γ}`.
* `angle_ineqs`: `0 < α`, `0 < β`, `α < γ`, `β < γ`, `π < 2γ` (`2γ = π + α`), `γ + β < π`, `γ < π − β`, `π/2 < γ`.
* FINDING W-1 control: `alpha_beta_order_free`: no lemma here compares `α` with `β`.
No sorry, no native_decide.
-/
import Erdos634.MarchSlots

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapAngles
open Erdos634.MarchSlots

variable {α β γ : ℝ}

theorem beta_eq (hA : AngleData α β γ) : β = (Real.pi - 3 * α) / 2 := by
  have := hA.hrel
  linarith

theorem gamma_eq (hA : AngleData α β γ) : γ = (Real.pi + α) / 2 := by
  have h := hA.hγdef
  have := hA.hrel
  linarith

/-- **the ledger (PROOF (0.2))** -/
theorem ledger (hA : AngleData α β γ) (x y z k : ℤ) :
    (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = (k : ℝ) * Real.pi ↔ 2 * x - 3 * y + z = 0 ∧ k = 2 * y - x := by
  have hb := beta_eq hA
  have hg := gamma_eq hA
  have hpi := Real.pi_pos
  constructor
  · intro h
    rw [hb, hg] at h
    have h1 : ((2 * x - 3 * y + z : ℤ) : ℝ) * α = ((2 * k - y - z : ℤ) : ℝ) * Real.pi := by
      push_cast
      linarith
    have hn : (2 * x - 3 * y + z : ℤ) = 0 := by
      by_contra hne
      apply hA.hirr
      have hne' : ((2 * x - 3 * y + z : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hne
      refine ⟨((2 * k - y - z : ℤ) : ℚ) / ((2 * x - 3 * y + z : ℤ) : ℚ), ?_⟩
      rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_intCast, div_mul_eq_mul_div, eq_div_iff hne']
      linarith
    refine ⟨hn, ?_⟩
    have h3 : ((2 * k - y - z : ℤ) : ℝ) * Real.pi = 0 := by
      rw [← h1, hn]; simp
    have h2 : (2 * k - y - z : ℤ) = 0 := by
      have : ((2 * k - y - z : ℤ) : ℝ) = 0 := by
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exact h4
        · exact absurd h4 hpi.ne'
      exact_mod_cast this
    omega
  · rintro ⟨h1, h2⟩
    have hz : z = 3 * y - 2 * x := by omega
    subst h2
    rw [hb, hg]
    have hzR : (z : ℝ) = 3 * y - 2 * x := by exact_mod_cast hz
    rw [hzR]
    push_cast
    ring

/-- **the two-sided ledger (PROOF 0.3)** -/
theorem ledger2 (hA : AngleData α β γ) (x y z x' y' z' k : ℤ) :
    (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = (x' : ℝ) * α + (y' : ℝ) * β + (z' : ℝ) * γ + (k : ℝ) * Real.pi ↔
      2 * (x - x') - 3 * (y - y') + (z - z') = 0 ∧ k = 2 * (y - y') - (x - x') := by
  have h := ledger hA (x - x') (y - y') (z - z') k
  rw [← h]
  push_cast
  constructor <;> intro h <;> linarith

theorem angle_ineqs (hA : AngleData α β γ) :
    0 < α ∧ 0 < β ∧ α < γ ∧ β < γ ∧ Real.pi < 2 * γ ∧ γ + β < Real.pi ∧ γ < Real.pi - β ∧ Real.pi / 2 < γ := by
  have ha := hA.hα
  have hb := hA.hβ
  have hg := gamma_eq hA
  have hr := hA.hrel
  have hpi := Real.pi_pos
  refine ⟨ha, hb, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-! ## Wedge fillings (natural multiplicities) -/

/-- a straight angle `π` is `{α, β, γ}` or `{3α, 2β}` -/
theorem fill_straight (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = Real.pi) :
    (x = 1 ∧ y = 1 ∧ z = 1) ∨ (x = 3 ∧ y = 2 ∧ z = 0) := by
  have := (ledger hA x y z 1).mp (by exact_mod_cast (by simpa using h : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ = ((1 : ℤ) : ℝ) * Real.pi))
  omega

/-- a wedge of size `γ` is one `γ` or `{α, α, β}` -/
theorem fill_gamma (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = γ) :
    (x = 0 ∧ y = 0 ∧ z = 1) ∨ (x = 2 ∧ y = 1 ∧ z = 0) := by
  have h2 := (ledger2 hA x y z 0 0 1 0).mp (by
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((0 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * β + ((1 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

/-- a wedge of size `3α` is `{α, α, α}` -/
theorem fill_3alpha (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = 3 * α) : x = 3 ∧ y = 0 ∧ z = 0 := by
  have h2 := (ledger2 hA x y z 3 0 0 0).mp (by
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((3 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

/-- a wedge of size `2α` is `{α, α}` -/
theorem fill_2alpha (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = 2 * α) : x = 2 ∧ y = 0 ∧ z = 0 := by
  have h2 := (ledger2 hA x y z 2 0 0 0).mp (by
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((2 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

/-- a wedge of size `α` is one `α` -/
theorem fill_alpha (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = α) : x = 1 ∧ y = 0 ∧ z = 0 := by
  have h2 := (ledger2 hA x y z 1 0 0 0).mp (by
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((1 : ℤ) : ℝ) * α + ((0 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

/-- a wedge of size `β` is one `β` -/
theorem fill_beta (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = β) : x = 0 ∧ y = 1 ∧ z = 0 := by
  have h2 := (ledger2 hA x y z 0 1 0 0).mp (by
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((0 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

/-- a wedge of size `α + β` is `{α, β}` -/
theorem fill_alpha_beta (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = α + β) : x = 1 ∧ y = 1 ∧ z = 0 := by
  have h2 := (ledger2 hA x y z 1 1 0 0).mp (by
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((1 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

/-- a wedge of size `π − β = 3α + β` is `{α, α, α, β}` or `{α, γ}` -/
theorem fill_pi_sub_beta (hA : AngleData α β γ) {x y z : ℕ}
    (h : (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * γ = Real.pi - β) :
    (x = 3 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) := by
  have h2 := (ledger2 hA x y z 3 1 0 0).mp (by
    have hr := hA.hrel
    have : ((x : ℤ) : ℝ) * α + ((y : ℤ) : ℝ) * β + ((z : ℤ) : ℝ) * γ =
        ((3 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ + ((0 : ℤ) : ℝ) * Real.pi := by
      push_cast; linarith
    exact this)
  omega

/-- two copies of `γ` never fit in a straight angle: `2γ > π` -/
theorem two_gamma_gt_pi (hA : AngleData α β γ) : Real.pi < 2 * γ := (angle_ineqs hA).2.2.2.2.1

/-- negative control: the ledger is false for `(x,y,z) = (1,1,0)` against `π` (it needs `2x − 3y + z = 0`) -/
example (hA : AngleData α β γ) : ¬ ((1 : ℝ) * α + (1 : ℝ) * β + (0 : ℝ) * γ = (1 : ℝ) * Real.pi) := by
  intro h
  have := (ledger hA 1 1 0 1).mp (by exact_mod_cast (by simpa using h : ((1 : ℤ) : ℝ) * α + ((1 : ℤ) : ℝ) * β + ((0 : ℤ) : ℝ) * γ = ((1 : ℤ) : ℝ) * Real.pi))
  omega

/-- witness: `AngleData` is satisfiable (the project's `angleData_f3`) and the straight fillings occur -/
example : ∃ α β γ : ℝ, AngleData α β γ := angleData_f3

#print axioms ledger
#print axioms ledger2
#print axioms fill_straight
#print axioms fill_pi_sub_beta

end Erdos634.Draft.WGapAngles
