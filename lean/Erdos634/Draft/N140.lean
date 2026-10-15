/-
Draft/N140.lean -- `N = 140` is NOT a tile count.

`140 = 4 · 35`.  Failing search-type leaves: S5 and `γ = 2α`.
* S5 `(t,e,f) = (2,17,18)`: member of the family `(2,k,k+1)`; its base has no word with two `c`-edges
  (`NSQM.s5word2_k`, `NSQM.raStatement_of_inst_trap2`); no certificate is used.
* every other S5 instance of `140` has `e = 1`, `f > t` and is dead by the γ-trap (`NSQM.s5word_e1`).
* `γ = 2α`: `M = 2`, `k = 17`, `GLK.caseG_of_leafOnly`.

No sorry, no native_decide.
-/
import Erdos634.Draft.N92
import Erdos634.Draft.RATrap
import Erdos634.Draft.RATrap2

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N140

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.N92

/-- **`RAStatementNsq 140`** (S5). -/
theorem ra : RAStatementNsq 140 := by
  refine raStatement_of_inst_trap2 140 ?_
  intro t e f ht he hef hcop hN hwb _
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 18 := by nlinarith
  have ht5 : t ≤ 7 := by
    by_contra h; push_neg at h
    have : 64 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  have hk : ¬ S5Word2 2 17 18 := s5word2_k (k := 17) (by norm_num)
  rcases eq_or_ne e 1 with he1 | he1
  · subst he1
    rcases lt_or_ge t f with htf | htf
    · exfalso; exact s5word_e1 (by omega) htf hwb.toWord
    · exfalso; interval_cases t <;> interval_cases f <;> omega
  · have he2 : 2 ≤ e := by omega
    interval_cases t <;> interval_cases f <;> interval_cases e <;>
      first | (norm_num at hN; done) | (exfalso; exact hk hwb)

theorem arith : ∀ M M' : ℤ, 0 < M → 0 < M' → ((140 : ℕ) : ℤ) = M * M' → (2 : ℤ) ∣ M - ((140 : ℕ) : ℤ) →
    (2 : ℤ) ∣ M' - ((140 : ℕ) : ℤ) → 3 * M < M' → M = 2 ∧ M' = 2 * (2 * ((17 : ℕ) : ℤ) + 1) := by
  intro M M' hM hM' hN h1 h2 h3
  push_cast at *
  have : M ≤ 7 := by nlinarith
  interval_cases M <;> omega

/-- `CaseGClosed 140` (`γ = 2α`). -/
theorem caseG : CaseGClosed 140 := Erdos634.GLK.caseG_of_leafOnly 140 17 (by norm_num) arith

/-- **`140` is not a tile count** (no `CongruentDissection 140` exists). -/
theorem not_tile_140 (D : CongruentDissection 140) : False :=
  not_tile_of_leaves 140 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapE60_of_chk' (by norm_num) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (rwStatement_nsq 140 (rwFree_of_chk (by decide +kernel))) ra caseG
    (gapE120_of_chk (by norm_num) (by decide +kernel)) D

end Erdos634.Draft.N140

#print axioms Erdos634.Draft.N140.not_tile_140
