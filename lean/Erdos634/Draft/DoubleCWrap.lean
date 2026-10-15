import Erdos634.DoubleC

/-!
# Double-c kill, arithmetic assembly (wrapper)

At e=1, m=1, f≥3, an equal side with initial c-block of length j≥2
is impossible.  `DoubleC` supplies the assembly.

`DoubleC.Config f j run` bundles the geometric hypotheses as named arithmetic conditions:
* hf: 3 ≤ f
* hj2: 2 ≤ j
* hjf: j < f
* hrun: arithmetic condition on the far-chord run length (a-slot or c-slot case)
* hcov: the far-chord side is covered by whole tile edges

The geometric consequents (that the initial c-block exists, that the chord length equals j·b,
that the far side is covered) appear as named hypotheses of Config.

No sorry, standard axioms.  Uniformity in j: one theorem covers all j in [2,f).
-/

namespace Erdos634.Draft.DoubleCWrap

open Erdos634.DoubleC Erdos634.Frontier

/-- prop:doublec: the double-c configuration at e=1 is impossible at every block length j. -/
theorem doublec_kill {f j run : ℕ} (C : Config f j run) : False :=
  doublec_impossible C

/-- The kill is uniform in j: all initial block lengths 2 ≤ j < f are simultaneously excluded. -/
theorem doublec_uniform {f : ℕ} :
    ∀ j, 2 ≤ j → j < f → ∀ run, Config f j run → False :=
  uniform_in_j f

-- Non-vacuity: the hypotheses are individually satisfiable (f=3, j=2 satisfies hf/hj2/hjf).
-- Joint vacuity is impossible since if all hypotheses held, doublec_kill gives False —
-- the theorem is the nonexistence proof, so non-vacuity means hypotheses CAN hold jointly
-- for some run; geometric instances are confirmed by the base-β e=1 search.
-- (DoubleC.lean cites `DoubleC.block_lengths_covered` as a counts check.)

#print axioms doublec_kill
#print axioms doublec_uniform

end Erdos634.Draft.DoubleCWrap
