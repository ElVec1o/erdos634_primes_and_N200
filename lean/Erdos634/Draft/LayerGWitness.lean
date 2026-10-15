/-
Draft/LayerGWitness.lean  In `AllThreshold`.

Witnesses for the hypotheses of the theorems of `Draft/LayerG.lean`, `Draft/LayerGChord.lean`, `Draft/LayerGPieces.lean` (project rule: a theorem whose hypotheses are unsatisfiable proves nothing).
The tilings used are the seeds of `UniformThreshold.betaTilable_self` (scale `f`, every member).

* `layer_c_i` at the members `(2, 3)` (`M = 3`, `b = 5 ≤ 18`) and `(3, 5)` (`M = 5`, `b = 16 ≤ 50`): `BetaTilable 2 3 5`, `BetaTilable 3 5 8`;
* `layer_c_ii` at the member `(2, 3)`, `M = 3`, `k = 1`: the congruent dissection of the frame triangle `T_5(2, 3)` with the chord uncrossed exists;
* `layer_pieces` at the member `(1, 2)` (`u = g = 1`), `M = 2` (`x_a = 1`): the counts `k3 = 2`, `k4 = 1`, `nA = 2`, `mA = 1`, `nB = 3`, `mB = 2`, `k6 = 1`, `l6 = k7 = l7 = 0` satisfy every hypothesis; the nine pieces have `(2 M e − e²)(3f² − e²) = 33` tiles;
* `layer_c_iii` at `f = 3`.

No sorry, no native_decide.
-/
import Erdos634.Draft.LayerGChord
import Erdos634.Draft.LayerGPieces

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.Draft.LayerG
open Erdos634.Draft.UniformThreshold (BetaTilable betaTilable_self)
open Erdos634.Draft.CollarG (ca cb)
open Erdos634.ChordTraceReal (straddlers)

/-- `prop:layerall` (c)(i) at the member `(2, 3)`: the seed at scale `3` gives a tiling at scale `5` -/
example : BetaTilable 2 3 5 :=
  layer_c_i 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (betaTilable_self (by norm_num) (by norm_num))

/-- `prop:layerall` (c)(i) at the member `(3, 5)`: the seed at scale `5` gives a tiling at scale `8` -/
example : BetaTilable 3 5 8 :=
  layer_c_i 3 5 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (betaTilable_self (by norm_num) (by norm_num))

/-- `prop:layerall` (c)(ii) at the member `(2, 3)`, `M = 3`, `k = 1`: the hypotheses are satisfied (the seed at scale `3`) and the right-hand side holds -/
example : ∃ (N : ℕ) (D : CongruentDissection N),
    straddlers D.toDissection (Erdos634.Draft.LayerE1Chord.skewX (Erdos634.Draft.CollarG.gF ((2 : ℕ) : ℝ) ((1 : ℕ) : ℝ)))
      (Erdos634.Draft.CollarG.cA ((2 : ℕ) : ℝ) ((1 : ℕ) : ℝ) * ((3 : ℕ) : ℝ)) = ∅ := by
  obtain ⟨N, D, -, -, h⟩ := (layer_c_ii 2 1 3 1 (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)).mp
    (betaTilable_self (by norm_num) (by norm_num))
  exact ⟨N, D, h⟩

/-- `prop:layerall` (b) at the member `(1, 2)`, `M = 2`: the hypotheses of `layer_pieces` are satisfied -/
example : ∃ (Λ : Set Plane) (N : ℕ) (R : Erdos634.Draft.RegionTiling.RTiling Λ
      (Erdos634.Draft.CollarG.Mod (u := (1 : ℝ)) (e := (1 : ℝ)) one_pos one_pos) N),
    (N : ℝ) = (2 * (2 : ℝ) * 1 - 1 ^ 2) * cP 1 1 := by
  obtain ⟨Λ, N, R, -, hN⟩ := layer_pieces (u := (1 : ℝ)) (g := (1 : ℝ)) (M := (2 : ℝ)) one_pos one_pos
    (by simp only [lxa]; norm_num) 2 1 2 1 3 2 1 0 0 0
    (by norm_num) (by norm_num [ca]) (by norm_num) (by norm_num) (by norm_num) (by norm_num [lxa])
    (by norm_num [cb]) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact ⟨Λ, N, R, hN⟩

/-- `prop:layerall` (c)(iii) at `f = 3` (`e = 2`): the condition of (b) at the scale `M = 3` -/
example : (3 ^ 2 + 2 * (3 - 1) * 3 ≤ 2 * 3 * 3 + (3 - 1) ^ 2 ↔ 3 ≤ 3) := (layer_c_iii 3 3 (by norm_num)).1

/-- `prop:layerall` (c)(iii) at `f = 3`: the condition of (c)(i), (c)(ii) at the scale `M = 1` -/
example : (3 ^ 2 - (3 - 1) ^ 2 ≤ 2 * 3 * 1 ↔ 1 ≤ 1) := (layer_c_iii 3 1 (by norm_num)).2.1

end Erdos634.Draft.LayerG

#print axioms Erdos634.Draft.LayerG.layer_c_iii
