/-
Draft/ChainGapA.lean -- the non-squarefree chain with the Case A leaf (`GapA N`) supplied as a statement.

`ChainIso.not_tile_nsq_full` obtains `GapA N` from a prime `ℓ ≥ 7` of odd valuation in `N`; `N = 120` and `N = 135`
have none.  Here `GapA N` is a hypothesis (for `N = 15 s²`, `30 s²` it is `GAUFinal.gapA_sq`).

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.E60Reduce

open scoped Classical

namespace Erdos634.Draft.ChainGapA

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF

/-- **Non-squarefree chain, Case A and all search-type leaves closed statements.** -/
theorem not_tile_nsq_gapA (N : ℕ) (hNQ : NQChk N) (hNSq : LeafNSq N) (hR : LeafR N) (hS2 : LeafS2 N)
    (gS1 : S1Closed N) (gS3 : S3Closed N) (gIso : IsoClosed N)
    (gS4 : RWStatementNsq N) (gS5 : RAStatementNsq N) (gG : CaseGClosed N)
    (gA : GapA N) (gE60 : GapE60 N) (gE120 : GapE120 N) (gF1 : GapF1 N) (gR8 : GapR8 N)
    (D : CongruentDissection N) : False := by
  have hNQ' : Erdos634.Geometry.NQ N := nq_of_chk hNQ
  have hN7 : 7 ≤ N := by
    obtain ⟨s, n, hs, -, hNs, h7, -⟩ := hNQ'
    have : 1 ≤ s ^ 2 := Nat.one_le_pow _ _ hs
    rw [hNs]; nlinarith
  have hN0 : 0 < N := by omega
  have hns : ¬ ∃ x y : ℕ, N = x ^ 2 + y ^ 2 := nsq_of_chk hNSq
  refine chain_nsq_iso N gS1 (s2Closed_of_arith N (s2Arith_of_chk hN0 hS2)) gS3 gIso gS4 gS5
    (fun _ => gA)
    (caseB_of_sumsq N (fun D μ τ hs => Row2.theoremS_perm_nsq D μ τ hs hNQ') hns)
    ?_ gG gE60 gE120 gF1 gR8 D
  rcases hR with hodd2 | ⟨hev, hnh⟩
  · exact caseR_of_odd N hodd2
  · exact caseR_of_H1 N (Erdos634.Draft.H1k.h1Right N) (nhsq_of_chk hev hnh)

end Erdos634.Draft.ChainGapA

#print axioms Erdos634.Draft.ChainGapA.not_tile_nsq_gapA
