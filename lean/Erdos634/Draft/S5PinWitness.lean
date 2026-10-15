/-
Draft/S5PinWitness.lean -- the two-`c`-edges theorem on a REAL S5 tiling (non-vacuity of its hypotheses), and a counterexample to an instance.

`FDCCevianAtom.atomTiles_four_scaled` is an exact `CongruentDissection` with 48 tiles, target sides `(12, 24, 24)` and
tile sides `(2, 3, 4)`: the S5 instance `(t, e, f) = (4, 1, 2)` (legs `t f (f²−e²) = 24`, base `t e (f²−e²) = 12`).

* `control_A4`: every hypothesis of `S5Family.s5_base_word2_hasSides` holds on this dissection, and the theorem
  returns a base word `12 = 2P + 3Q + 4R` with `R ≥ 2`.  So the hypotheses of `S5PinC.base_two_c` are satisfiable
  by a real object, and the theorem does not exclude a real tiling.
* `s5word2_4_1_2`: the word condition holds at `(4,1,2)` (`12 = 2·2 + 4·2`), so `s5inst_of_no_word2` does NOT
  apply there; `not_s5inst_4_1_2`: indeed `S5Inst 4 1 2` is false.

No sorry, no native_decide.
-/
import Erdos634.Draft.S5Family
import Erdos634.Draft.FDCCevianAtom

namespace Erdos634.Draft.NSQM

open Erdos634.Geometry Erdos634.Draft.FDBBaseBetaE1

/-- **Positive control**: the real 48-tile S5 tiling `(4,1,2)` satisfies the hypotheses, and its base has a word
with at least two `c`-edges. -/
theorem control_A4 : ∃ D : CongruentDissection G3CAtomTiling.tiles.length,
    HasSides D.target 24 24 12 ∧ HasSides D.model 2 3 4 ∧ S5Word2 4 1 2 := by
  obtain ⟨D, h1, h2⟩ := Erdos634.Draft.FDCCevianAtom.atomTiles_four_scaled
  have hT : HasSides D.target 24 24 12 := hasSides_rot h1
  refine ⟨D, hT, h2, ?_⟩
  refine s5_base_word2_hasSides (t := 4) (e := 1) (f := 2) (by norm_num) (by norm_num) (by norm_num)
    ⟨-1, 1, by norm_num⟩ D ?_ ?_
  · convert hT using 1 <;> norm_num
  · convert h2 using 1 <;> norm_num

/-- the word condition holds at `(4,1,2)`: `12 = 2·2 + 3·0 + 4·2` -/
theorem s5word2_4_1_2 : S5Word2 4 1 2 := ⟨2, 0, 2, le_refl 2, by norm_num⟩

/-- **Counterexample**: the S5 instance `(4,1,2)` HAS a dissection, so `S5Inst 4 1 2` is false. -/
theorem not_s5inst_4_1_2 : ¬ S5Inst 4 1 2 := by
  intro h
  obtain ⟨D, hT, hM, -⟩ := control_A4
  refine s5inst_hasSides h D ?_ ?_
  · convert hT using 1 <;> norm_num
  · convert hM using 1 <;> norm_num

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.control_A4
#print axioms Erdos634.Draft.NSQM.not_s5inst_4_1_2
