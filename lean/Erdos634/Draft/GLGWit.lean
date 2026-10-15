import Erdos634.Draft.GLGMain

/-!
# GLG witness: the model hypotheses of `leafG_model_empty` are satisfiable at `k = 3` (N = 28, tile (9,7,12)) without `G*`

Explicit survivor (G_MIXED_NOTES §3.3 at `k = 3`, found by search): `La = b b b a c` (flips 0,0,0,0,1), `Lb = c c a a`
(0,0,1,1), base `c b a a c b` (0,0,0,0,1,1).  `Model 3` holds (every rule incl. sums) and `GStar Lb` FAILS
(`Lb` reads `c, c, a`): `G*` is exactly what excludes the mixed family.  NOT a tiling; a boundary configuration of the model only.
-/

namespace Erdos634.GLG

def mk (l : List TT) (f : List Bool) : Side :=
  ⟨l.length, fun i => l.getD i .a, fun i => f.getD i false⟩

def WLa : Side := mk [.b, .b, .b, .a, .c] [false, false, false, false, true]
def WLb : Side := mk [.c, .c, .a, .a] [false, false, true, true]
def WBa : Side := mk [.c, .b, .a, .a, .c, .b] [false, false, false, false, true, true]

theorem vWLa : WLa.V := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;>
  · have h' : i + 1 < 5 := hi
    have : i < 5 := by omega
    interval_cases i <;> decide
theorem vWLb : WLb.V := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;>
  · have h' : i + 1 < 4 := hi
    have : i < 3 := by omega
    interval_cases i <;> decide
theorem vWBa : WBa.V := by
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩ <;>
  · have h' : i + 1 < 6 := hi
    have : i < 5 := by omega
    interval_cases i <;> decide

theorem witness_model : Model 3 WLa WLb WBa :=
  ⟨by decide, by decide, by decide, vWLa, vWLb, vWBa, by decide, by decide, by decide, by decide, by decide,
   by decide, fun _ => by decide, fun _ => by decide, fun _ => by decide, fun _ => by decide,
   by decide, by decide⟩

/-- `G*` fails on the witness's `Lb`: the survivor is not excluded by the rules `V, C0, C2, K` alone. -/
theorem witness_not_gstar : ¬ GStar WLb := by
  intro h
  have := h (by simp [WLb, mk]) (by simp [WLb, mk]) (by simp [WLb, mk])
  simp [WLb, mk, Side.sa, sAng, ends] at this

end Erdos634.GLG
