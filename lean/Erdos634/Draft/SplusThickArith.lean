/-
Credit: D. Paliy (2026-10-03 to 10-08, W/beta caps, exact boundary-adjacency and thick-member observations; public repository github.com/DenisUkranian/erdos-634-tilings), M. Beeson and G. Rosu.
Draft/SplusThickArith.lean -- written 19 October 2026.  UNAUDITED.  Not in `All`; in `AllSplusThick`.

**Arithmetic of the side `AQ` of `W_M(e, f)` when `M (f - e) < f`** (fix G2 of the audit `project working notes`).
`SideRunGArith.C_AQ` assumes `M (f - e) ≤ e`; its proof uses the hypothesis only to get `(M - m)(f - e) < f` for `WStripArith.count_no_b_int`,
so it holds verbatim under `M (f - e) < f`.  This is the NEW lemma `C_AQ'` (the old file is not edited).

Credit: Beeson-Rosu (framework, cor:thickw), the E2R6 room, Chisel, the S+ audit.  No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunGArith

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SplusThick
open Erdos634.Draft.SideRunGArith Erdos634.Draft.WStripArith

/-- **(C-AQ'), the weakened hypothesis `M (f - e) < f`**: a representation of `M f b` has `f ∣ y`, and if `M (f - e) < f` then `z ≤ M (f - e)`. -/
theorem C_AQ' {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2)) :
    f ∣ y ∧ (M * (f - e) < f → z ≤ M * (f - e)) := by
  obtain ⟨b, hbN, hbZ⟩ := exists_b hef
  rw [hbN] at h
  have hZ : (x : ℤ) * (e * f) + y * (b : ℤ) + z * (f : ℤ) ^ 2 = M * f * (b : ℤ) := by exact_mod_cast h
  rw [hbZ] at hZ
  have hF : (0 : ℤ) < f := by omega
  have hef' : (e : ℤ) < f := by omega
  have hy0 : (0 : ℤ) ≤ y := by positivity
  have hd : (f : ℤ) ∣ (e : ℤ) ^ 2 * (y : ℤ) :=
    ⟨(y : ℤ) * f - M * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) + x * e + z * f, by
      linear_combination (-1 : ℤ) * hZ⟩
  have hdy : (f : ℤ) ∣ (y : ℤ) := dvd_of_coprime_mul_sq hco hd
  refine ⟨by exact_mod_cast hdy, fun hMe => ?_⟩
  obtain ⟨m, hm⟩ := hdy
  have hm0 : 0 ≤ m := nonneg_of_eq_mul hF hy0 hm
  have h2 : (f : ℤ) * ((x : ℤ) * e + z * f) = (f : ℤ) * (((M : ℤ) - m) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2)) := by
    linear_combination hZ - ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) * hm
  have h3 : (x : ℤ) * e + z * f = ((M : ℤ) - m) * ((f : ℤ) ^ 2 - (e : ℤ) ^ 2) :=
    mul_left_cancel₀ hF.ne' h2
  have hcast : ((M * (f - e) : ℕ) : ℤ) = (M : ℤ) * ((f : ℤ) - e) := by
    rw [Nat.cast_mul, Nat.cast_sub hef.le]
  have hMe' : (M : ℤ) * ((f : ℤ) - e) < f := by
    rw [← hcast]
    exact_mod_cast hMe
  have hmfe : (0 : ℤ) ≤ m * ((f : ℤ) - e) := mul_nonneg hm0 (by omega)
  have hN : ((M : ℤ) - m) * ((f : ℤ) - e) < f := by nlinarith
  obtain ⟨-, hz1⟩ := count_no_b_int (N := (M : ℤ) - m) (X := (x : ℤ)) (Z := (z : ℤ)) hef hco
    (by positivity) hN h3
  have hzle : (z : ℤ) ≤ M * ((f : ℤ) - e) := by nlinarith
  rw [← hcast] at hzle
  exact_mod_cast hzle

/-- the arithmetic of the corollary (N1): `M < f`, `M (f - e) ≤ e + 1`, a representation of `M f b` with `z ≥ e + 2` is impossible -/
theorem no_rep_z_ge {e f M x y z : ℕ} (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f)
    (hMf : M < f) (hM : M * (f - e) ≤ e + 1)
    (h : x * (e * f) + y * (f ^ 2 - e ^ 2) + z * f ^ 2 = M * f * (f ^ 2 - e ^ 2))
    (hz : e + 1 ≤ z) (hz2 : e + 2 ≤ f → e + 2 ≤ z) : False := by
  have hlt : M * (f - e) < f := by
    rcases Nat.lt_or_ge (e + 1) f with h1 | h1
    · omega
    · -- e + 1 = f : M * 1 = M < f
      have hfe : f - e = 1 := by omega
      rw [hfe]; omega
  have hz' := (C_AQ' he hef hco h).2 hlt
  by_cases h2 : e + 2 ≤ f
  · have := hz2 h2; omega
  · have hfe : f = e + 1 := by omega
    have h1 : f - e = 1 := by omega
    rw [h1] at hz'
    omega

-- hypotheses satisfiable: (5,8,2), (5,7,3), (7,11,2), (8,11,3), control (3,5,2)
example : Nat.Coprime 5 8 ∧ 2 ≤ 5 ∧ 5 < 8 ∧ 2 < 8 ∧ 8 ≤ 2 * 5 ∧ 2 * (8 - 5) ≤ 5 + 1 := by decide
example : Nat.Coprime 5 7 ∧ 2 ≤ 5 ∧ 5 < 7 ∧ 3 < 7 ∧ 7 ≤ 3 * 5 ∧ 3 * (7 - 5) ≤ 5 + 1 := by decide
example : Nat.Coprime 7 11 ∧ 2 ≤ 7 ∧ 7 < 11 ∧ 2 < 11 ∧ 11 ≤ 2 * 7 ∧ 2 * (11 - 7) ≤ 7 + 1 := by decide
example : Nat.Coprime 8 11 ∧ 2 ≤ 8 ∧ 8 < 11 ∧ 3 < 11 ∧ 11 ≤ 3 * 8 ∧ 3 * (11 - 8) ≤ 8 + 1 := by decide
example : Nat.Coprime 3 5 ∧ 2 ≤ 3 ∧ 3 < 5 ∧ 2 < 5 ∧ 5 ≤ 2 * 3 ∧ 2 * (5 - 3) ≤ 3 + 1 := by decide

end Erdos634.Draft.SplusThick

#print axioms Erdos634.Draft.SplusThick.C_AQ'
#print axioms Erdos634.Draft.SplusThick.no_rep_z_ge
