/-
Draft/E60Reduce.lean -- the non-squarefree chain with every leaf except `GapE60` supplied by kernel-checked arithmetic.

`not_tile_of_e60 N`: if the arithmetic leaves of `N` hold (`NQChk`, `EllChk2`, `LeafNSq`, `LeafHAr`, `LeafR`, `LeafS2`,
`S1Chk`, `LeafS3`, `LeafIso`, `RWChk`, `S5pChk`, `GammaChk`, `Pairs120Chk`, `LeafF1p`, `LeafR8z`), then `N` is not a tile
count as soon as `GapE60 N` holds (no tile with an angle `π/3` and an irrational angle cuts an equilateral triangle
into `N`).  A wrapper of `ChainIso.not_tile_nsq_full`; used for `N = 168, 198`, whose only failing leaf is `GapE60`.
`not_tile_of_e60_s5_g N`: the same with the S5 leaf (`RAStatementNsq N`) and the `γ = 2α` leaf (`CaseGClosed N`) also
supplied as closed statements (for `N = 171`).

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.N566076
import Erdos634.Draft.ChainIso
import Erdos634.Draft.R8ZFLeaf

open scoped Classical

namespace Erdos634.Draft.E60Reduce

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.IsoInst Erdos634.Draft.ChainIso Erdos634.Draft.R8ZF

theorem gapF1_of_leaf {N : ℕ} (h6 : 6 < N) (h : LeafF1p N) : GapF1 N := by
  rcases h with h4 | hf
  · exact gapF1_of_mod4_two N h4
  · exact gapF1_of_chkpar h6 hf

/-- **Every leaf except `GapE60` by arithmetic.** -/
theorem not_tile_of_e60 (N : ℕ) (hN : 6 < N) (hNQ : NQChk N) (hEll : EllChk2 N) (hNSq : LeafNSq N) (hHAr : LeafHAr N)
    (hR : LeafR N) (hS2 : LeafS2 N) (hS1 : S1Chk N) (hS3 : LeafS3 N) (hIso : LeafIso N) (hRW : RWChk N)
    (hRA : S5pChk N) (hG : GammaChk N) (h120 : Pairs120Chk N) (hF1 : LeafF1p N) (hR8 : LeafR8z N)
    (gE60 : GapE60 N) (D : CongruentDissection N) : False :=
  not_tile_nsq_full N hNQ hEll hNSq hHAr hR hS2 (s1Closed_of_free N (s1Free_of_chk hS1))
    (s3Closed_of_isoQRef N (isoQRef_of_chk (by omega) hS3)) (isoClosed_of_chk (by omega) hIso)
    (rwStatement_nsq N (rwFree_of_chk hRW)) (raStatement_nsqM N (s5pFree_of_chk hRA))
    (caseG_of_gammaArith N (gammaArith_of_chk hG)) gE60 (gapE120_of_chk (by omega) h120)
    (gapF1_of_leaf hN hF1) (gapR8_of_chk_z hR8.1 hR8.2.1 hR8.2.2) D

/-- **Every leaf except `GapE60`, the S5 leaf and the `γ = 2α` leaf by arithmetic.** -/
theorem not_tile_of_e60_s5_g (N : ℕ) (hN : 6 < N) (hNQ : NQChk N) (hEll : EllChk2 N) (hNSq : LeafNSq N)
    (hHAr : LeafHAr N) (hR : LeafR N) (hS2 : LeafS2 N) (hS1 : S1Chk N) (hS3 : LeafS3 N) (hIso : LeafIso N)
    (hRW : RWChk N) (h120 : Pairs120Chk N) (hF1 : LeafF1p N) (hR8 : LeafR8z N)
    (gS5 : RAStatementNsq N) (gG : CaseGClosed N) (gE60 : GapE60 N) (D : CongruentDissection N) : False :=
  not_tile_nsq_full N hNQ hEll hNSq hHAr hR hS2 (s1Closed_of_free N (s1Free_of_chk hS1))
    (s3Closed_of_isoQRef N (isoQRef_of_chk (by omega) hS3)) (isoClosed_of_chk (by omega) hIso)
    (rwStatement_nsq N (rwFree_of_chk hRW)) gS5 gG gE60 (gapE120_of_chk (by omega) h120)
    (gapF1_of_leaf hN hF1) (gapR8_of_chk_z hR8.1 hR8.2.1 hR8.2.2) D

end Erdos634.Draft.E60Reduce

#print axioms Erdos634.Draft.E60Reduce.not_tile_of_e60
