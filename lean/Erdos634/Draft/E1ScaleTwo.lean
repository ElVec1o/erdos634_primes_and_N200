/-
Draft/E1ScaleTwo.lean -- the threshold statement at scale TWO for every member `(1, f)` of the base-β row.

    theorem not_betaTilable_1_f_2 : 3 ≤ f → ¬ BetaTilable 1 f 2
    theorem thresholdAt_1_f_2     : 2 ≤ f → ThresholdAt 1 f 2
    theorem thresholdAt_e1_of     : 2 ≤ f → 1 ≤ M → (2 * M < f ∨ M = 2 ∨ f ≤ M) → ThresholdAt 1 f M

`T_2(1,f)`, the isosceles triangle with legs `2f³` and base `2(3f² − 1)`, has no tiling by `(f, f² − 1, f²)` for
every `f ≥ 3`: for `f ≥ 5` this is the side theorem (`Draft.SideRun.not_betaTilable_e1_two`, a proof); for `f = 3`
and `f = 4` it is a kernel-checked search certificate (`NotUniform104.notuniform_104`, `Refl.MS1N188`).  At `f = 2`
the scale `2` is the scale `f`, where a tiling exists.  Composite side; not prime-case work.
No sorry, no native_decide.
-/
import Erdos634.Draft.SideRun
import Erdos634.Draft.NotUniform104
import Erdos634.Draft.N188
import Erdos634.Draft.CollarE1

namespace Erdos634.Draft.E1ScaleTwo

open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord Erdos634.Draft.FDBBaseBetaE1
open Erdos634.Draft.UniformThreshold

/-- member `(1,3)`: no tiling at scale `2` (certificate of `N = 104`) -/
theorem not_betaTilable_1_3_2 : ¬ BetaTilable 1 3 2 := by
  rintro ⟨N, D, hT, hM⟩
  exact Erdos634.Draft.NotUniform104.notuniform_104 D
    ⟨hasSides_congr hT (by norm_num) (by norm_num) (by norm_num),
      hasSides_congr hM (by norm_num) (by norm_num) (by norm_num)⟩

/-- member `(1,4)`: no tiling at scale `2` (certificate of `N = 188`) -/
theorem not_betaTilable_1_4_2 : ¬ BetaTilable 1 4 2 := by
  rintro ⟨N, D, hT, hM⟩
  have hT' : HasSides D.target 128 128 94 := hasSides_congr hT (by norm_num) (by norm_num) (by norm_num)
  have hM' : HasSides D.model 4 15 16 := hasSides_congr hM (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨g1, g2, g3⟩ := Erdos634.Draft.N188.TGT_S1
  obtain ⟨k1, k2, k3⟩ := Refl.MS1N188.MODEL_sides
  exact Refl.MS1N188.not_dissection D (congruent_of_hasSides' hT' g1 g2 g3)
    (congruent_of_hasSides' (hasSides_rot hM') k1 k2 k3)

/-- **`T_2(1,f)` has no tiling, for every `f ≥ 3`.** -/
theorem not_betaTilable_1_f_2 (f : ℕ) (hf : 3 ≤ f) : ¬ BetaTilable 1 f 2 := by
  by_cases h5 : 5 ≤ f
  · exact Erdos634.Draft.SideRun.not_betaTilable_e1_two f h5
  · have h : f = 3 ∨ f = 4 := by omega
    rcases h with rfl | rfl
    · exact not_betaTilable_1_3_2
    · exact not_betaTilable_1_4_2

/-- **The threshold statement at scale two holds for every member `(1, f)`.** -/
theorem thresholdAt_1_f_2 (f : ℕ) (hf : 2 ≤ f) : ThresholdAt 1 f 2 := by
  by_cases h3 : 3 ≤ f
  · exact ⟨fun hB => absurd hB (not_betaTilable_1_f_2 f h3), fun h => by omega⟩
  · have h2 : f = 2 := by omega
    subst h2
    exact ⟨fun _ => le_rfl, fun _ => betaTilable_self le_rfl (by norm_num)⟩

/-- **The threshold statement for the members `(1, f)` at the scales `2M < f`, `M = 2` and `M ≥ f`.**  What is left
for `e = 1` is `f/2 ≤ M < f`, `M ≥ 3`. -/
theorem thresholdAt_e1_of (f M : ℕ) (hf : 2 ≤ f) (hM : 1 ≤ M) (h : 2 * M < f ∨ M = 2 ∨ f ≤ M) :
    ThresholdAt 1 f M := by
  rcases h with h | h | h
  · exact Erdos634.Draft.SideRun.thresholdAt_e1_half f M hM h
  · subst h; exact thresholdAt_1_f_2 f hf
  · exact ⟨fun _ => h, fun _ => Erdos634.Draft.CollarE1.betaTilable_e1 f hf M h⟩

end Erdos634.Draft.E1ScaleTwo

#print axioms Erdos634.Draft.E1ScaleTwo.not_betaTilable_1_f_2
#print axioms Erdos634.Draft.E1ScaleTwo.thresholdAt_1_f_2
#print axioms Erdos634.Draft.E1ScaleTwo.thresholdAt_e1_of
