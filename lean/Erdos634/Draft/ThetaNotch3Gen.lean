-- Draft/ThetaNotch3Gen.lean -- STAGE 2: the general statement `theta_t(e,f)` tiled for every `t >= t0(e,f)` (case rho >= 1).
-- INTERNAL BUILD ONLY, UNAUDITED.  No sorry, no native_decide.
/-
`t0(e,f) = j0 f + M0` with `n0 = ceil(e/g)`, `j0 = ceil(n0 e / b)`, `M0 = max(ceil(f n0 / e), n0 + ceil(e n0 / f))`, `g = f - e`, `b = f^2 - e^2`
(`internal notes` 2.1).  The parameter set `(j0, M0, n0, n1 = floor(e M0 / f), s = j0 f + n0, rho = e M0 mod f)` satisfies `NP3cond` whenever `rho >= 1`.
**What is covered**: every `1 <= e < f` whose `rho = e M0 mod f` is nonzero.  **What is not**: `rho = 0`.  There the pieces `rho-tau`,
`rho-par` are absent; the old `NP` (ThetaNotchMain, `n1 = n`, strict (b), (c)) covers it IF `n1 = n0` and `(b), (c)` are strict -- true for every
`e < f <= 700` by computation (4000 rows) but NOT proved here for all `(e,f)`.
Superseded 2026-11-14: for e = 1 by `ThetaNotch4E1.rho0f_one` / `thetaTiled_general_rho0_e1`, for coprime e >= 2 `rho0f e f != 0` by `ThetaNotch4Rho.rho0f_ne_zero`; the closed statement is `ThetaNotch4Rho.thetaTiled_all`.
CREDIT: Paliy, Beeson, Laczkovich, Zhang, Beeson-Rosu; the project.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch3Inst

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled)

theorem ceil_facts (a b : ℕ) (hb : 0 < b) : a ≤ b * ((a + b - 1) / b) ∧ b * ((a + b - 1) / b) < a + b := by
  have h1 := Nat.div_add_mod (a + b - 1) b
  have h2 := Nat.mod_lt (a + b - 1) hb
  constructor <;> omega

/-- `n0 = ceil(e / (f - e))` -/
def n0f (e f : ℕ) : ℕ := (e + (f - e) - 1) / (f - e)
/-- `j0 = ceil(n0 e / b)` -/
def j0f (e f : ℕ) : ℕ := (n0f e f * e + (f * f - e * e) - 1) / (f * f - e * e)
/-- `M0 = max(ceil(f n0 / e), n0 + ceil(e n0 / f))` -/
def M0f (e f : ℕ) : ℕ := max ((f * n0f e f + e - 1) / e) (n0f e f + (e * n0f e f + f - 1) / f)
/-- the threshold `t0(e,f) = j0 f + M0` -/
def t0f (e f : ℕ) : ℕ := j0f e f * f + M0f e f
/-- `rho = e M0 mod f` -/
def rho0f (e f : ℕ) : ℕ := (e * M0f e f) % f

theorem np3cond_formula (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hr : rho0f e f ≠ 0) :
    NP3cond e f (M0f e f) (n0f e f) (e * M0f e f / f) (j0f e f) (j0f e f * f + n0f e f) (rho0f e f) := by
  have hg : 0 < f - e := by omega
  have hbpos : 0 < f * f - e * e := by
    have : e * e < f * f := Nat.mul_self_lt_mul_self hef
    omega
  have hfpos : 0 < f := by omega
  have hepos : 0 < e := by omega
  obtain ⟨n1a, n1b⟩ := ceil_facts e (f - e) hg
  have hn0 : e ≤ (f - e) * n0f e f := by unfold n0f; exact n1a
  have hn0p : 1 ≤ n0f e f := by
    by_contra hc
    have h0 : n0f e f = 0 := by omega
    rw [h0] at hn0; simp at hn0; omega
  obtain ⟨j1a, j1b⟩ := ceil_facts (n0f e f * e) (f * f - e * e) hbpos
  have hj0 : n0f e f * e ≤ (f * f - e * e) * j0f e f := by unfold j0f; exact j1a
  have hnepos : 1 ≤ n0f e f * e := Nat.mul_pos hn0p hepos
  have hj0p : 1 ≤ j0f e f := by
    by_contra hc
    have h0 : j0f e f = 0 := by omega
    rw [h0] at hj0; simp at hj0; omega
  obtain ⟨xa, xb⟩ := ceil_facts (f * n0f e f) e hepos
  obtain ⟨ya, yb⟩ := ceil_facts (e * n0f e f) f hfpos
  have hepn : 1 ≤ e * n0f e f := Nat.mul_pos hepos hn0p
  have hyp : 1 ≤ (e * n0f e f + f - 1) / f := Nat.div_pos (by omega) hfpos
  have hMx : (f * n0f e f + e - 1) / e ≤ M0f e f := le_max_left _ _
  have hMy : n0f e f + (e * n0f e f + f - 1) / f ≤ M0f e f := le_max_right _ _
  have hfn : f * n0f e f ≤ e * M0f e f := by
    calc f * n0f e f ≤ e * ((f * n0f e f + e - 1) / e) := xa
      _ ≤ e * M0f e f := Nat.mul_le_mul_left _ hMx
  have hn1 : n0f e f ≤ e * M0f e f / f := by
    rw [Nat.le_div_iff_mul_le hfpos]; linarith [mul_comm f (n0f e f)]
  have hdm := Nat.div_add_mod (e * M0f e f) f
  have hml := Nat.mod_lt (e * M0f e f) hfpos
  have hhC : e * n0f e f ≤ f * (M0f e f - n0f e f) := by
    have : f * ((e * n0f e f + f - 1) / f) ≤ f * (M0f e f - n0f e f) := Nat.mul_le_mul_left _ (by omega)
    exact le_trans ya this
  have hMn : n0f e f < M0f e f := by omega
  have hsplit : f * M0f e f = f * n0f e f + f * (M0f e f - n0f e f) := by
    rw [← Nat.mul_add]; congr 1; omega
  refine ⟨he, hef, hn0p, hn1, hn0, ?_, ?_, ?_, hj0p, ?_, ?_, ?_, ?_, ?_⟩
  · unfold rho0f; exact hdm.symm
  · exact Nat.pos_of_ne_zero hr
  · unfold rho0f; exact hml
  · have := hn0p; omega
  · omega
  · calc e * n0f e f = n0f e f * e := Nat.mul_comm _ _
      _ ≤ (f * f - e * e) * j0f e f := hj0
      _ = j0f e f * (f * f - e * e) := Nat.mul_comm _ _
  · have h3 : (j0f e f * f + n0f e f) * f = j0f e f * f * f + n0f e f * f := by ring
    have h4 : (M0f e f + j0f e f * f) * f = M0f e f * f + j0f e f * f * f := by ring
    rw [h3, h4]
    nlinarith [hsplit, hhC, mul_comm f (M0f e f), mul_comm f (n0f e f)]
  · have h5 : e + (f - e) * (j0f e f * f) ≤ (f - e) * (j0f e f * f + n0f e f) := by
      rw [Nat.mul_add]; omega
    exact h5

/-- **Theorem N, case rho >= 1 (Stage 2).**  For `1 <= e < f` with `rho = e M0 mod f != 0`, `theta_t(e,f)` is tiled by the tile `(e f, f^2-e^2, f^2)`
for every `t >= t0(e,f) = j0 f + M0`. -/
theorem thetaTiled_general (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hr : rho0f e f ≠ 0) :
    ∀ t, t0f e f ≤ t → ThetaTiled e f (f * f - e * e) t := by
  intro t ht
  refine thetaTiled_of_cond e f (M0f e f) (n0f e f) (e * M0f e f / f) (j0f e f) (j0f e f * f + n0f e f) (rho0f e f)
    (np3cond_formula e f he hef hr) t ?_
  unfold t0f at ht; omega

theorem tileCount_general (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hr : rho0f e f ≠ 0) (t : ℕ) (ht : t0f e f ≤ t) :
    Erdos634.Draft.TileCountFamilies.TileCount ((f * f - e * e) * t * t) := by
  obtain ⟨D, -, -⟩ := thetaTiled_general e f he hef hr t ht
  exact ⟨D⟩

/-! ### consistency: the formula reproduces the table of `internal notes` 2.2 -/
theorem t0f_table : t0f 1 2 = 4 ∧ t0f 2 3 = 7 ∧ t0f 3 4 = 14 ∧ t0f 4 5 = 18 ∧ t0f 5 6 = 28 ∧ t0f 3 8 = 11 ∧ t0f 5 7 = 13 ∧ t0f 7 10 = 16 ∧
    t0f 1 6 = 12 ∧ t0f 3 5 = 9 ∧ t0f 2 5 = 8 := by decide

/-- witnesses for the hypothesis `rho != 0` (the general theorem is applicable): -/
theorem rho_witnesses : rho0f 2 3 ≠ 0 ∧ rho0f 3 4 ≠ 0 ∧ rho0f 4 5 ≠ 0 ∧ rho0f 5 6 ≠ 0 ∧ rho0f 3 8 ≠ 0 ∧ rho0f 5 7 ≠ 0 ∧ rho0f 7 10 ≠ 0 := by decide

/-- negative control: at `e = 1` we have `rho = 0` (the general theorem does NOT apply; the old `NP` does) -/
theorem rho_zero_e1 : rho0f 1 2 = 0 ∧ rho0f 1 3 = 0 ∧ rho0f 1 6 = 0 := by decide

theorem thetaTiled_2_3_general : ∀ t, 7 ≤ t → ThetaTiled 2 3 5 t := by
  have := thetaTiled_general 2 3 (by norm_num) (by norm_num) (by decide)
  simpa [t0f_table.2.1] using this

end

end Erdos634.Draft.ThetaNotch
