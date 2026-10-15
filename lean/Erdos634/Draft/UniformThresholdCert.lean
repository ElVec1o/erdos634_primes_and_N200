/-
Draft/UniformThresholdCert.lean: the threshold statement for the base-β row: the cases that need search
certificates (scale two for `f ≤ 4`), and the summary for the members with `f = 3`.

    theorem not_betaTilable_two : (e,f) ∈ {(1,3), (2,3), (1,4), (3,4)} → ¬ BetaTilable e f 2
    theorem threshold_f3  : e ∈ {1, 2} → 1 ≤ M → M ≤ 3 → ThresholdAt e 3 M
    theorem threshold_1_3 : 1 ≤ M → ThresholdAt 1 3 M          -- the member (1,3), every scale
    theorem threshold_f3_mul : e ∈ {1, 2} → 0 < k → ThresholdAt e 3 (3 k)
    theorem threshold_f4_le_two : e ∈ {1, 3} → 1 ≤ M → M ≤ 2 → ThresholdAt e 4 M

    theorem threshold_2_3_of_ne_four : 1 ≤ M → M ≠ 4 → ThresholdAt 2 3 M      -- the member (2,3), all scales but one
    theorem threshold_2_3_iff : (∀ M ≥ 1, ThresholdAt 2 3 M) ↔ BetaTilable 2 3 4
    theorem threshold_1_4_of_ne_three, threshold_1_4_iff : (∀ M ≥ 1, ThresholdAt 1 4 M) ↔ ¬ BetaTilable 1 4 3
    theorem threshold_3_4_of : 1 ≤ M → M ∉ {3, 5, 6, 9} → ThresholdAt 3 4 M
    theorem threshold_3_4_iff : (∀ M ≥ 1, ThresholdAt 3 4 M) ↔ ¬ BetaTilable 3 4 3   -- with `Draft.Residue`

    theorem threshold_2_3 : 1 ≤ M → ThresholdAt 2 3 M          -- the member (2,3), every scale (with `Draft.W23`)

For the member `(1, 3)` the statement `BetaTilable 1 3 M ↔ 3 ≤ M` is a theorem for every `M ≥ 1` (the tilings at
`M ≥ 3` are `Draft.W13`: two kernel-checked collar tilings and the addition of W-triangles).  For the member `(2, 3)`
the statement is a theorem for every `M ≥ 1` with `Draft.W23` and `Draft.CollarG`.  For `f = 4` it is a theorem at `M = 1, 2`.

Imports the large certificate of `156` (through `BaseBetaScale2`): built in `AllCert1`, not in `All`.
No sorry, no native_decide.
-/
import Erdos634.Draft.UniformThreshold
import Erdos634.Draft.BaseBetaScale2
import Erdos634.Draft.W13
import Erdos634.Draft.CollarG
import Erdos634.Draft.W23
import Erdos634.Draft.ThresholdReduce
import Erdos634.Draft.ResidueSeed

open scoped Classical

namespace Erdos634.Draft.UniformThreshold

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1

/-- **Scale two, `3 ≤ f ≤ 4`**: no tiling (four kernel-checked certificates). -/
theorem not_betaTilable_two {e f : ℕ}
    (h : (e = 1 ∧ f = 3) ∨ (e = 2 ∧ f = 3) ∨ (e = 1 ∧ f = 4) ∨ (e = 3 ∧ f = 4)) : ¬ BetaTilable e f 2 := by
  rintro ⟨N, D, hT, hM⟩
  exact Erdos634.Draft.BaseBetaScale2.basebeta_scale_two h D
    ⟨hasSides_congr hT (by push_cast; ring) (by push_cast; ring) (by push_cast; ring), hM⟩

/-- **The members with `f = 3`, scales `1, 2, 3`**: a tiling exists exactly at scale `3`. -/
theorem threshold_f3 {e : ℕ} (he : e = 1 ∨ e = 2) {M : ℕ} (h1 : 1 ≤ M) (h3 : M ≤ 3) : ThresholdAt e 3 M := by
  have hco : Nat.Coprime e 3 := by rcases he with rfl | rfl <;> decide
  have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he3 : e < 3 := by rcases he with rfl | rfl <;> norm_num
  have hM : M = 1 ∨ M = 2 ∨ M = 3 := by omega
  rcases hM with rfl | rfl | rfl
  · exact threshold_one hco he1 he3
  · refine ⟨fun h => absurd h (not_betaTilable_two ?_), fun h => by omega⟩
    rcases he with rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  · refine ⟨fun _ => le_rfl, fun _ => ?_⟩
    rcases he with rfl | rfl
    · exact betaTilable_1_3_three
    · exact betaTilable_2_3_three

/-- **The member `(1, 3)`: the threshold statement at EVERY scale.**  The base-β target with legs `27 M` and base
`26 M` is cut into copies of `(3, 8, 9)` if and only if `M ≥ 3`. -/
theorem threshold_1_3 {M : ℕ} (h1 : 1 ≤ M) : ThresholdAt 1 3 M := by
  by_cases h3 : M ≤ 3
  · exact threshold_f3 (Or.inl rfl) h1 h3
  · exact ⟨fun _ => by omega, fun _ => Erdos634.Draft.W13.betaTilable_1_3_ge M (by omega)⟩

/-- the members with `f = 3` at every multiple of `3` -/
theorem threshold_f3_mul {e : ℕ} (he : e = 1 ∨ e = 2) {k : ℕ} (hk : 0 < k) : ThresholdAt e 3 (k * 3) :=
  ⟨fun _ => by nlinarith, fun _ => betaTilable_f3_mul he hk⟩

/-- **The members with `f = 4`, scales `1, 2`**: no tiling. -/
theorem threshold_f4_le_two {e : ℕ} (he : e = 1 ∨ e = 3) {M : ℕ} (h1 : 1 ≤ M) (h2 : M ≤ 2) :
    ThresholdAt e 4 M := by
  have hco : Nat.Coprime e 4 := by rcases he with rfl | rfl <;> decide
  have he1 : 1 ≤ e := by rcases he with rfl | rfl <;> norm_num
  have he4 : e < 4 := by rcases he with rfl | rfl <;> norm_num
  have hM : M = 1 ∨ M = 2 := by omega
  rcases hM with rfl | rfl
  · exact threshold_one hco he1 he4
  · refine ⟨fun h => absurd h (not_betaTilable_two ?_), fun h => by omega⟩
    rcases he with rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-! ## After the collar (`Draft.CollarG`): what is left for `f ≤ 4` -/

/-- **The member `(2, 3)`: the threshold statement at every scale except `M = 4`.** -/
theorem threshold_2_3_of_ne_four {M : ℕ} (h1 : 1 ≤ M) (h4 : M ≠ 4) : ThresholdAt 2 3 M := by
  by_cases h3 : M ≤ 3
  · exact threshold_f3 (Or.inr rfl) h1 h3
  · exact ⟨fun _ => by omega, fun _ => Erdos634.Draft.CollarG.betaTilable_2_3 M (by omega) h4⟩

/-- the member `(2, 3)`: the threshold statement at every scale is equivalent to ONE tiling, of the base-β target at
scale `4` (legs `108`, base `184`, `368` tiles `(6, 5, 9)`) -/
theorem threshold_2_3_iff : (∀ M, 1 ≤ M → ThresholdAt 2 3 M) ↔ BetaTilable 2 3 4 := by
  constructor
  · intro h
    exact (h 4 (by norm_num)).mpr (by norm_num)
  · intro h M h1
    by_cases h4 : M = 4
    · rw [h4]; exact ⟨fun _ => by norm_num, fun _ => h⟩
    · exact threshold_2_3_of_ne_four h1 h4

/-- **The member `(2, 3)`: the threshold statement at EVERY scale.**  The base-β target with legs `27 M` and base
`46 M` is cut into copies of `(6, 5, 9)` if and only if `M ≥ 3`.  (Scale `4`: the kernel-checked tiling of
`Draft.W23`.) -/
theorem threshold_2_3 {M : ℕ} (h1 : 1 ≤ M) : ThresholdAt 2 3 M :=
  threshold_2_3_iff.mpr Erdos634.Draft.W23.betaTilable_2_3_4 M h1

/-- control of `ThresholdReduce.not_betaTilable_of_cert`: the certificate of `N = 92` (member `(2, 3)`, scale `2`)
through the interface -/
theorem not_betaTilable_2_3_two_interface : ¬ BetaTilable 2 3 2 := by
  obtain ⟨g1, g2, g3⟩ := Erdos634.Draft.N92.TGT_S1N92
  obtain ⟨k1, k2, k3⟩ := Refl.MS1N92.MODEL_sides
  refine Erdos634.Draft.ThresholdReduce.not_betaTilable_of_cert Refl.MS1N92.TGT Refl.MS1N92.MODEL ?_ ?_
    (fun D hT hM => Refl.MS1N92.not_dissection D hT hM)
  · have h : HasSides Refl.MS1N92.TGT 92 54 54 :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact g2,
        by simp only [Equiv.refl_apply]; rw [dist_comm]; exact g3, by simp only [Equiv.refl_apply]; exact g1⟩
    exact hasSides_congr (hasSides_rot h) (by norm_num) (by norm_num) (by norm_num)
  · have h : HasSides Refl.MS1N92.MODEL 5 9 6 :=
      ⟨Equiv.refl _, by simp only [Equiv.refl_apply]; exact k2,
        by simp only [Equiv.refl_apply]; rw [dist_comm]; exact k3, by simp only [Equiv.refl_apply]; exact k1⟩
    exact hasSides_congr (hasSides_rot (hasSides_rot h)) (by norm_num) (by norm_num) (by norm_num)

/-- **The member `(1, 4)`: the threshold statement at every scale except `M = 3`.** -/
theorem threshold_1_4_of_ne_three {M : ℕ} (h1 : 1 ≤ M) (h3 : M ≠ 3) : ThresholdAt 1 4 M := by
  by_cases h2 : M ≤ 2
  · exact threshold_f4_le_two (Or.inl rfl) h1 h2
  · exact ⟨fun _ => by omega, fun _ => Erdos634.Draft.CollarE1.betaTilable_e1 4 (by norm_num) M (by omega)⟩

/-- the member `(1, 4)`: the threshold statement at every scale is equivalent to ONE exclusion, at scale `3`
(legs `192`, base `141`, `N = 423`) -/
theorem threshold_1_4_iff : (∀ M, 1 ≤ M → ThresholdAt 1 4 M) ↔ ¬ BetaTilable 1 4 3 := by
  constructor
  · intro h hB
    have := (h 3 (by norm_num)).mp hB
    omega
  · intro h M h1
    by_cases h3 : M = 3
    · rw [h3]; exact ⟨fun hB => absurd hB h, fun h' => by omega⟩
    · exact threshold_1_4_of_ne_three h1 h3

/-- **The member `(3, 4)`**: the threshold statement at every scale except `M = 3` (an exclusion, `N = 351`) and
`M = 5, 6, 9`, by the collar alone.  The scales `5, 6, 9` are `threshold_3_4_of_ne_three` below (residue seeds). -/
theorem threshold_3_4_of {M : ℕ} (h1 : 1 ≤ M) (h3 : M ≠ 3) (h5 : M ≠ 5) (h6 : M ≠ 6) (h9 : M ≠ 9) :
    ThresholdAt 3 4 M := by
  by_cases h2 : M ≤ 2
  · exact threshold_f4_le_two (Or.inr rfl) h1 h2
  by_cases h10 : 10 ≤ M
  · exact Erdos634.Draft.CollarG.thresholdAt_large 3 4 (by norm_num) (by norm_num) (by decide) M (by omega)
  · have hM : M = 4 ∨ M = 7 ∨ M = 8 := by omega
    rcases hM with rfl | rfl | rfl
    · exact Erdos634.Draft.CollarG.thresholdAt_lin 3 4 (by norm_num) (by norm_num) 1 le_rfl 0
    · exact Erdos634.Draft.CollarG.thresholdAt_lin 3 4 (by norm_num) (by norm_num) 1 le_rfl 1
    · exact Erdos634.Draft.CollarG.thresholdAt_lin 3 4 (by norm_num) (by norm_num) 2 (by norm_num) 0

/-- **The member `(3, 4)`: the threshold statement at every scale except `M = 3`** (collar and residue seeds:
`Draft.Residue.thresholdAt_ge`). -/
theorem threshold_3_4_of_ne_three {M : ℕ} (h1 : 1 ≤ M) (h3 : M ≠ 3) : ThresholdAt 3 4 M := by
  by_cases h2 : M ≤ 2
  · exact threshold_f4_le_two (Or.inr rfl) h1 h2
  · exact Erdos634.Draft.Residue.thresholdAt_ge 3 4 (by norm_num) (by norm_num) (by decide) M (by omega)

/-- the member `(3, 4)`: the threshold statement at every scale is equivalent to ONE exclusion, at scale `3`
(legs `192`, base `351`, `N = 351`) -/
theorem threshold_3_4_iff : (∀ M, 1 ≤ M → ThresholdAt 3 4 M) ↔ ¬ BetaTilable 3 4 3 := by
  constructor
  · intro h hB
    have := (h 3 (by norm_num)).mp hB
    omega
  · intro h M h1
    by_cases h3 : M = 3
    · rw [h3]; exact ⟨fun hB => absurd hB h, fun h' => by omega⟩
    · exact threshold_3_4_of_ne_three h1 h3

end Erdos634.Draft.UniformThreshold

#print axioms Erdos634.Draft.UniformThreshold.threshold_3_4_iff
#print axioms Erdos634.Draft.UniformThreshold.not_betaTilable_two
#print axioms Erdos634.Draft.UniformThreshold.threshold_f3
#print axioms Erdos634.Draft.UniformThreshold.threshold_f4_le_two
#print axioms Erdos634.Draft.UniformThreshold.threshold_1_3
#print axioms Erdos634.Draft.UniformThreshold.threshold_2_3_iff
#print axioms Erdos634.Draft.UniformThreshold.threshold_1_4_iff
#print axioms Erdos634.Draft.UniformThreshold.threshold_3_4_of
#print axioms Erdos634.Draft.UniformThreshold.threshold_2_3
#print axioms Erdos634.Draft.UniformThreshold.not_betaTilable_2_3_two_interface
