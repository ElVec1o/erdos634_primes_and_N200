-- Witness and counterexample for `ADMCore.admissible_alpha_tgt` / `admissible_beta_tgt` on the certified
-- 2673-tile tiling (G3CIsoControl): tile (3,5,7)*1890, target (189,189,297)*1890 = 27*1890*(7,7,11);
-- 2673 = 3 * 9^2 * 11 = d' w^2 (2a+b) with a = 3 = 3*1^2, w = 9, k = d' e' w = 27.
import Erdos634.Draft.ADMCore
import Erdos634.Draft.G3CIsoControl

open scoped Classical

namespace Erdos634.Draft.ADMControl

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.G3CIsoControl
open Erdos634.Draft.ADMCore

theorem sq3 : Squarefree 3 := Irreducible.squarefree Nat.prime_three
theorem sq5 : Squarefree 5 := Irreducible.squarefree Nat.prime_five

theorem hm3 : D.model.TwoPiThreeData α ((1890 : ℝ) * ((3 : ℕ) : ℝ)) ((1890 : ℝ) * ((5 : ℕ) : ℝ))
    ((1890 : ℝ) * ((7 : ℕ) : ℝ)) := by
  simpa only [Nat.cast_ofNat] using data

/-- The target is the base-beta isosceles target of the tile (3,5,7): base angles `pi/3 - alpha`. -/
theorem tgt_beta : TgtAngles D (Real.pi / 3 - α) (Real.pi / 3 - α)
    ((Real.pi / 3 - α) + 3 * (Real.pi / 3 - (Real.pi / 3 - α))) := by
  refine ⟨1, ?_, ?_, ?_⟩
  · simp only [Equiv.Perm.coe_one, id_eq]
    rw [← hβ]; exact Erdos634.Draft.G3CAng.angle_eq_of_cos 0 (σm 1) (t_cos0.trans cos_β.symm)
  · simp only [Equiv.Perm.coe_one, id_eq]
    rw [← hβ]; exact Erdos634.Draft.G3CAng.angle_eq_of_cos 1 (σm 1) (t_cos1.trans cos_β.symm)
  · simp only [Equiv.Perm.coe_one, id_eq]
    have h0 : D.target.angleAt 0 = β :=
      Erdos634.Draft.G3CAng.angle_eq_of_cos 0 (σm 1) (t_cos0.trans cos_β.symm)
    have h1 : D.target.angleAt 1 = β :=
      Erdos634.Draft.G3CAng.angle_eq_of_cos 1 (σm 1) (t_cos1.trans cos_β.symm)
    have hs := D.target.angleAt_sum
    rw [hβ] at h0 h1
    linarith

/-- **Witness, base-beta clause**, on the real 2673-tiling: all hypotheses of `admissible_beta_tgt` hold
(`(a,b,c)=(3,5,7)`, `a = 3*1^2`, `d'=3` squarefree) and the conclusion gives `k = 27`, `w = 9`. -/
theorem witness_beta :
    ∃ k w : ℕ, D.target.BaseAlphaData (Real.pi / 3 - α) ((1890 : ℝ) * ((5 : ℕ) : ℝ))
        ((1890 : ℝ) * ((3 : ℕ) : ℝ)) ((1890 : ℝ) * ((7 : ℕ) : ℝ)) (k : ℝ) ∧ 0 < w ∧
      k = 3 * 1 * w ∧ G3CIso2673.cert.leaves.length = 3 * w ^ 2 * (2 * 3 + 5) ∧
      ((1 : ℕ) : ℤ) ∣ w * (((7 : ℕ) : ℤ) - (3 : ℕ) - (5 : ℕ)) ∧
      (2 : ℤ) ∣ (w * (((7 : ℕ) : ℤ) - (3 : ℕ) - (5 : ℕ))) / ((1 : ℕ) : ℤ) - (G3CIso2673.cert.leaves.length : ℕ) :=
  admissible_beta_tgt D 3 5 7 3 1 1890 α (by norm_num) (by norm_num) (by norm_num)
    sq3 hm3 tgt_beta

/-- The concrete values: `w = 9`, `k = 27`. -/
theorem witness_beta_values : ∃ k w : ℕ, k = 27 ∧ w = 9 ∧
    D.target.BaseAlphaData (Real.pi / 3 - α) ((1890 : ℝ) * ((5 : ℕ) : ℝ))
        ((1890 : ℝ) * ((3 : ℕ) : ℝ)) ((1890 : ℝ) * ((7 : ℕ) : ℝ)) (k : ℝ) := by
  obtain ⟨k, w, hb, hw, hk, hN, -, -⟩ := witness_beta
  rw [G3CIso2673.cert_len] at hN
  have hw2 : w ^ 2 = 81 := by omega
  have hw9 : w = 9 := by nlinarith
  exact ⟨k, w, by omega, hw9, hb⟩

/-- **Witness, base-alpha clause**, same tiling read through the swapped tile `(5,3,7)`:
`b = 3 = 3*1^2`, `N = 3 w^2 (5+6) = 2673`. -/
theorem witness_alpha :
    ∃ k w : ℕ, D.target.BaseAlphaData (Real.pi / 3 - α) ((1890 : ℝ) * ((5 : ℕ) : ℝ))
        ((1890 : ℝ) * ((3 : ℕ) : ℝ)) ((1890 : ℝ) * ((7 : ℕ) : ℝ)) (k : ℝ) ∧ 0 < w ∧
      k = 3 * 1 * w ∧ G3CIso2673.cert.leaves.length = 3 * w ^ 2 * (5 + 2 * 3) := by
  have hm' := twoPiThreeData_swap hm3
  have := admissible_alpha_tgt D 5 3 7 3 1 1890 (Real.pi / 3 - α) (by norm_num) (by norm_num)
    (by norm_num) sq3 hm' tgt_beta
  obtain ⟨k, w, hb, hw, hk, hN, -, -⟩ := this
  exact ⟨k, w, hb, hw, hk, hN⟩

/-- **Counterexample.**  With the WRONG labelling `(a,b) = (3,5)` the same target is NOT the base-alpha
target of the tile: if it were, `admissible_alpha_tgt` (`d = 5`, `e = 1`) would give `2673 = 5 w^2 13`,
but `5 ∤ 2673`.  So the clause `N = d w^2 (a+2b)` has teeth on a real tiling. -/
theorem control_wrong_alpha_reading :
    ¬ TgtAngles D α α (α + 3 * (Real.pi / 3 - α)) := by
  intro ht
  obtain ⟨k, w, -, -, -, hN, -, -⟩ := admissible_alpha_tgt D 3 5 7 5 1 1890 α (by norm_num)
    (by norm_num) (by norm_num) sq5 hm3 ht
  rw [G3CIso2673.cert_len] at hN
  have h5 : (65 : ℕ) ∣ 2673 := ⟨w ^ 2, by linarith [hN]⟩
  revert h5; norm_num

theorem control_N : (2673 : ℕ) = 3 ^ 5 * 11 := by norm_num

end Erdos634.Draft.ADMControl

#print axioms Erdos634.Draft.ADMControl.witness_beta
#print axioms Erdos634.Draft.ADMControl.witness_beta_values
#print axioms Erdos634.Draft.ADMControl.witness_alpha
#print axioms Erdos634.Draft.ADMControl.control_wrong_alpha_reading
