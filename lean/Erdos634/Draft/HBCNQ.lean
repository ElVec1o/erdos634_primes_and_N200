/-
Draft/HBCNQ.lean -- HBC item (2): `NQ N -> HBSimilar N` (one-line corollary of `Row2.theoremS_perm_nsq`), and the N = 60
chain with `CaseBClosed 60` (hence `HBSimilarRest 60`) discharged by it.  Remaining hypotheses: exactly the other leaves
GapA, CaseG, GapE60, GapE120, GapF1, GapR8, RA60, RW60.
-/
import Erdos634.Draft.NSQCaseB
import Erdos634.Draft.CompositeN60

open scoped Classical

namespace Erdos634.Draft.HBCNQ

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.ChainComposite

/-- `HBSimilar` on the range of Lemma Q, exactly `Row2.theoremS_perm_nsq`. -/
theorem hbSimilar_of_NQ {N : ℕ} (h : NQ N) : HBSimilar N :=
  fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs h

/-- The corrected statement: `HBSimilar` is false at `N = 3 s^2` (see `HBCFalse3`), so the honest general form
exempts those `N`.  (Not claimed proved for all other `N`; `hbSimilar_of_NQ` proves it on `NQ N`.) -/
def HBSimilar' (N : ℕ) : Prop := (∀ s : ℕ, N ≠ 3 * s ^ 2) → HBSimilar N

theorem hbSimilar'_of_NQ_sqfree {N : ℕ} (h : NQ N) : HBSimilar N := hbSimilar_of_NQ h

theorem nq60 : NQ 60 :=
  ⟨2, 15, by norm_num, by decide +kernel, by norm_num, by norm_num, Or.inr (Or.inr (by norm_num))⟩

theorem nsq60 : ¬ ∃ x y : ℕ, 60 = x ^ 2 + y ^ 2 := by
  rintro ⟨x, y, h⟩
  have hx : x ≤ 8 := by nlinarith
  have hy : y ≤ 8 := by nlinarith
  interval_cases x <;> interval_cases y <;> omega

theorem caseB_60 : CaseBClosed 60 := caseB_of_sumsq 60 (hbSimilar_of_NQ nq60) nsq60

/-- **N = 60 chain, Case B discharged**; no `HBSimilarRest`, no `CaseBClosed` hypothesis. -/
theorem chain_60_final_nq (gA : Erdos634.Draft.Chain15.GapA 60) (gG : CaseGClosed 60)
    (gE60 : Erdos634.Draft.Chain15.GapE60 60) (gE120 : Erdos634.Draft.Chain15.GapE120 60)
    (gF1 : Erdos634.Draft.Chain15.GapF1 60) (gR8 : Erdos634.Draft.Chain15.GapR8 60)
    (gRA : Erdos634.Draft.CompositeN60.RA60) (gRW : Erdos634.Draft.CompositeN60.RW60)
    (D : CongruentDissection 60) : False :=
  Erdos634.Draft.CompositeN60.chain_60_final gA caseB_60 gG gE60 gE120 gF1 gR8 gRA gRW D

end Erdos634.Draft.HBCNQ

#print axioms Erdos634.Draft.HBCNQ.hbSimilar_of_NQ
#print axioms Erdos634.Draft.HBCNQ.chain_60_final_nq
