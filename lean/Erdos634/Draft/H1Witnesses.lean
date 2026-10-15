/-
Satisfiability checks for the atoms `H1aSetup`, `H1bCaseAB`, `H1dCaseD`.
  * H1.a: the real `CongruentDissection 2` `dissection'` (α456) satisfies `RightNormal` and `RightCase`; the extraction
    yields `RightFacts 2 1 ...` (so `M = 1`, `lam = 1`: the rational branch).
  * H1.b: `a = 1, b = 2, c = lam = √5` (the N = 10 tile (1,2), `lam = √5`): all hypotheses of `caseAB_sumsq` hold; the
    conclusion `5 = 1² + 2²` is the expected one.
  * H1.d: arithmetic witness `a = √3, b = 1, c = 2, lam = √3` (`r = 0, s = 2`, `u = (2,0,0)`, `w = (2,0,0)`).  This only
    shows the ALGEBRAIC hypotheses of `caseD_algebra` are consistent; Case D is geometrically impossible (steps D4–D9).
 No sorry.
-/
import Erdos634.Draft.H1aSetup
import Erdos634.Draft.H1bCaseAB
import Erdos634.Draft.H1dCaseD
import Erdos634.Draft.FluxGRow3RPAnyLabelWitness

open scoped Classical

namespace Erdos634.Draft.H1Witnesses

open Erdos634.Geometry Erdos634.CertCoord Erdos634.AngleThreshold
open Erdos634.Draft.FluxGRow3AngleWitnessDissection Erdos634.Draft.FluxGRow3WitnessBridge
open Erdos634.Draft.FluxGRow3SharedGrid Erdos634.Draft.FluxGRow3Step3N2Final
open Erdos634.Draft.FluxRow4Witness Erdos634.Geometry.Row3 Erdos634.Draft.FluxGRow3RPWitness

theorem rightNormal_witness : H1a.RightNormal dissection' α456 :=
  ⟨α456_pos, α456_lt_pi_div_two, α456_div_pi_irr, model'_angleAt0, tile0'_angleAt2,
    target_angleAt0, target_angleAt1⟩

theorem rightCase_witness : Erdos634.Draft.TheoremPConditional.RightCase dissection' :=
  ⟨α456, α456_pos, α456_lt_pi_div_two, α456_div_pi_irr, ⟨0, 2, by decide, model'_angleAt0, tile0'_angleAt2⟩,
    α456, Or.inl rfl, 0, 1, by decide, target_angleAt0, target_angleAt1⟩

/-- The extraction on the real witness, and the forced value `M = 1`. -/
theorem facts_witness : ∃ M : ℕ, M = 1 ∧ H1a.RightFacts 2 M (dissection'.model.oppLen 0)
    (dissection'.model.oppLen 1) (dissection'.model.oppLen 2)
    (dissection'.target.oppLen 1 / dissection'.model.oppLen 2) := by
  obtain ⟨M, hM⟩ := rightNormal_witness.facts
  exact ⟨M, by have := hM.hN; omega, hM⟩

theorem rightCase_facts_witness : ∃ (D' : CongruentDissection 2) (α : ℝ) (M : ℕ), H1a.RightNormal D' α :=
  let ⟨D', α, M, h, _⟩ := H1a.rightCase_facts rightCase_witness
  ⟨D', α, M, h⟩

/-- H1.b hypotheses are satisfiable: tile `(1, 2, √5)`, `lam = √5`, `M = 5`. -/
theorem caseAB_witness : ∃ x y : ℕ, 5 = x ^ 2 + y ^ 2 := by
  have h5 : Irrational (Real.sqrt 5) := by
    have := Nat.Prime.irrational_sqrt (p := 5) (by norm_num)
    simpa using this
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  exact H1b.caseAB_sumsq (M := 5) (a := 1) (b := 2) (c := Real.sqrt 5) (lam := Real.sqrt 5)
    (by norm_num) (by norm_num) (by rw [hs]; norm_num) (by positivity) (by rw [hs]; norm_num) h5
    ⟨1 / 2, by norm_num⟩ ⟨1, 2, 0, by ring_nf; rw [hs]⟩

/-- H1.d hypotheses are (algebraically) satisfiable. -/
theorem caseD_witness :
    ∃ (K : IntermediateField ℚ ℝ) (hl : Real.sqrt 3 ∈ K) (ht : Real.sqrt 3 / 1 ∈ K) (hct : (2 : ℝ) / 1 ∈ K)
      (σ : K →ₐ[ℚ] ℝ), σ ⟨Real.sqrt 3, hl⟩ = -Real.sqrt 3 := by
  have h3 : Irrational (Real.sqrt 3) := by
    have := Nat.Prime.irrational_sqrt (p := 3) (by norm_num)
    simpa using this
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  obtain ⟨K, hl, ht, hct, σ, -, h1, -⟩ := H1d.caseD_algebra (a := Real.sqrt 3) (b := 1) (c := 2)
    (lam := Real.sqrt 3) (r := 0) (s := 2) (M := 3) (ua := 2) (ub := 0) (uc := 0) (wa := 2) (wb := 0) (wc := 0)
    (by norm_num) (by norm_num) (by rw [hs]; norm_num) (by norm_num) (by simpa using h3)
    (by positivity) hs h3 (by ring) (by ring)
  exact ⟨K, hl, ht, hct, σ, h1⟩

end Erdos634.Draft.H1Witnesses

#print axioms Erdos634.Draft.H1Witnesses.rightCase_facts_witness
#print axioms Erdos634.Draft.H1Witnesses.facts_witness
#print axioms Erdos634.Draft.H1Witnesses.caseAB_witness
#print axioms Erdos634.Draft.H1Witnesses.caseD_witness
