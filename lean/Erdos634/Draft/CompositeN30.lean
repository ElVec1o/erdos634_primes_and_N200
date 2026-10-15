/-
Draft/CompositeN30.lean -- N = 30 = 2*3*5 (squarefree, N % 4 = 2): the strongest chain with every leaf proved EXCEPT Case A.
  `chain_30_final (gA : GapAcomp 30)` has the single residual hypothesis `GapAcomp 30`
  (= LemmaSStatement -> GapA 30; the 5-smooth Case A leaf at N = 30: no prime l >= 7 of odd valuation, so `gapA_of_ell(E)` does not apply).
  Discharged here: S1 (l = 5, 3 QNR mod 5), S2 (l = 5), S3 (IsoQRef 30 by check), IsoH9 30 by check, Case B (HBSimilar via
  sqfree >= 17, 30 not a sum of two squares), Right (H1k.h1Right, 15 not x^2+y^2), gamma=2alpha / pi/3 / 2pi/3-equilateral / F1
  (N % 4 = 2 parity), GapR8 30 (NoF2, NoF3, NoF4z by finite arithmetic; NoF4 FAILS at 30 = 5*6 but NoF4z holds: x=1,y=4 gives 21).
  CONDITIONAL.  No sorry, no native_decide. ***
-/
import Erdos634.Draft.CompositeNine

open scoped Classical

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeN30

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith
open Erdos634.Draft.CompositeFinal2 Erdos634.Draft.R8Gen2

theorem sqfree_30 : Squarefree (30 : ℕ) := by decide +kernel
theorem isoH9_30 : IsoH9 30 := isoH9_of_check 30 (by norm_num) (by decide +kernel)
theorem isoQRef_30 : IsoQRef 30 := isoQRef_of_check 30 (by norm_num) (by norm_num) (by decide +kernel)
theorem nsq30 : ¬ ∃ x y : ℕ, 30 = x ^ 2 + y ^ 2 := nsq 30 (by norm_num) (by decide)
theorem nsqh30 : ¬ ∃ x y : ℕ, 30 = 2 * (x ^ 2 + y ^ 2) := nsq_half 30 (by norm_num) (by decide)
theorem hbSimilar_30 : HBSimilar 30 := Erdos634.CaseA.RComposite.hbSimilar_of_sqfree17 sqfree_30 (by norm_num)

theorem noF3_30 : NoF3 30 := by
  intro s j hj hjs h
  push_cast at h
  have h1 : j ≤ 4 := by nlinarith
  have h2 : s ≤ 12 := by nlinarith
  interval_cases j <;> interval_cases s <;> omega

theorem noF2_30 : NoF2 30 := by
  apply noF2_of_int
  · intro z hz
    push_cast at hz
    have h1 : z ≤ 6 := by nlinarith
    have h2 : -6 ≤ z := by nlinarith
    interval_cases z <;> omega
  · intro x r hx hr h z hz
    push_cast at hz
    have hx7 : x ≤ 6 := by nlinarith
    have hr9 : r ≤ 9 := by nlinarith
    interval_cases x <;> interval_cases r <;> omega

theorem noF4z_30 : NoF4z 30 := by
  apply noF4z_of_int
  intro x r hx hr h z hz
  have hx7 : x ≤ 6 := by nlinarith
  have hr9 : r ≤ 9 := by nlinarith
  interval_cases x <;> interval_cases r <;>
    first
    | omega
    | (norm_num at hz
       have h1 : z ≤ 6 := by nlinarith
       have h2 : -6 ≤ z := by nlinarith
       interval_cases z <;> omega)

theorem gapR8_30 : GapR8 30 := gapR8_of_arith2 30 noF2_30 noF3_30 noF4z_30

/-- **N = 30, modulo `GapAcomp 30` (Case A) only.** -/
theorem chain_30_final (gA : GapAcomp 30) (D : CongruentDissection 30) : False :=
  chain_gen2 30 sqfree_30 5 (by norm_num) (val_one (p := 5) (k := 6) (by norm_num) (by norm_num) (by norm_num))
    qnr3_5
    (s2Closed_of_qnr 30 5 (by norm_num) (val_one (p := 5) (k := 6) (by norm_num) (by norm_num) (by norm_num))
      qnr2_5 qnr3_5)
    (s3Closed_of_isoQRef 30 isoQRef_30) isoH9_30
    gA (caseB_of_sumsq 30 hbSimilar_30 nsq30) (caseR_of_H1 30 (Erdos634.Draft.H1k.h1Right 30) nsqh30)
    (caseG_of_mod4_two 30 (by norm_num)) (gapE60_of_mod4_two 30 (by norm_num))
    (gapE120_of_mod4_two 30 (by norm_num)) (gapF1_of_mod4_two 30 (by norm_num)) gapR8_30 D

end Erdos634.Draft.CompositeN30

#print axioms Erdos634.Draft.CompositeN30.chain_30_final
