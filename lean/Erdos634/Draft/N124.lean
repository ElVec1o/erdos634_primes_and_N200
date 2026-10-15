/-
Draft/N124.lean -- `N = 124` is NOT a tile count.

`124 = 4 · 31`.  Failing search-type leaves: S4, S5 and `γ = 2α`.
* S4 `(S',e,f) = (2,1,4)`: tile (4,15,16) in (120,62,128) -- certificate `Refl.MC124.not_dissection` (2,010 nodes).
* S5 `(t,e,f) = (2,15,16)`: member of the family `(2,k,k+1)`; its base has no word with two `c`-edges
  (`NSQM.s5word2_k`, `NSQM.raStatement_of_inst_trap2`); no certificate is used.
* every other S5 instance of `124` has `e = 1`, `f > t` and is dead by the γ-trap (`NSQM.s5word_e1`).
* `γ = 2α`: `M = 2`, `k = 15`, `GLK.caseG_of_leafOnly`.

No sorry, no native_decide.
-/
import Erdos634.Draft.N92
import Erdos634.Draft.RATrap
import Erdos634.Draft.RATrap2
import Erdos634.Refl.MC124Sound
import Erdos634.Draft.HasSidesPerm

open scoped Classical
set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.N124

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.ChainComposite
open Erdos634.Draft.CompositeGen2 Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeS2Arith
open Erdos634.Draft.CompositeS1Arith Erdos634.Draft.CompositeIsoB Erdos634.Draft.CompositeFinal2
open Erdos634.Draft.CompositeFinal3 Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN2
open Erdos634.Draft.NSQRA Erdos634.Draft.NSQRW Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.NSQLegs
open Erdos634.Draft.NSQMain Erdos634.Draft.NSQM Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.N566076 Erdos634.Draft.N92

/-- **`RAStatementNsq 124`** (S5). -/
theorem ra : RAStatementNsq 124 := by
  refine raStatement_of_inst_trap2 124 ?_
  intro t e f ht he hef hcop hN hwb _
  push_cast at hN
  have hd : 2 * f - 1 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht4 : 4 ≤ t ^ 2 := by nlinarith
  have hf : f ≤ 16 := by nlinarith
  have ht5 : t ≤ 8 := by
    by_contra h; push_neg at h
    have : 81 ≤ t ^ 2 := by nlinarith
    nlinarith
  have hf2 : 2 ≤ f := by omega
  have hk : ¬ S5Word2 2 15 16 := s5word2_k (k := 15) (by norm_num)
  rcases eq_or_ne e 1 with he1 | he1
  · subst he1
    rcases lt_or_ge t f with htf | htf
    · exfalso; exact s5word_e1 (by omega) htf hwb.toWord
    · exfalso; interval_cases t <;> interval_cases f <;> omega
  · have he2 : 2 ≤ e := by omega
    interval_cases t <;> interval_cases f <;> interval_cases e <;>
      first | (norm_num at hN; done) | (exfalso; exact hk hwb)

theorem TGT_C : dist (Refl.MC124.TGT.pts 0) (Refl.MC124.TGT.pts 1) = 62 ∧
    dist (Refl.MC124.TGT.pts 1) (Refl.MC124.TGT.pts 2) = 128 ∧ dist (Refl.MC124.TGT.pts 0) (Refl.MC124.TGT.pts 2) = 120 :=
  model_sides_rp Refl.MC124.hDn Refl.MC124.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

open Erdos634.Draft.FDBBaseBetaE1 in
/-- S4 `(S',e,f) = (2,1,4)`: tile `(4,15,16)`, target `(120,62,128)`. -/
theorem s4inst_2_1_4 : S4Inst 2 1 4 := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := TGT_C
  obtain ⟨k1, k2, k3⟩ := Refl.MC124.MODEL_sides
  have hT : HasSides D.target 62 120 128 :=
    hasSides_of_oppLen (by rw [h0]; norm_num) (by rw [h1]; norm_num) (by rw [h2]; norm_num)
  have hM : HasSides D.model 4 15 16 :=
    hasSides_of_sigma σ (by rw [m0]; norm_num) (by rw [m1]; norm_num) (by rw [m2]; norm_num)
  exact Refl.MC124.not_dissection D
    (congruent_of_hasSides' (hasSides_rot (hasSides_rot (hasSides_swap hT))) g1 g2 g3)
    (congruent_of_hasSides' (hasSides_rot hM) k1 k2 k3)

/-- **`RWStatementNsq 124`** (S4): the scaled instance `(2,1,4)`. -/
theorem rw124 : RWStatementNsq 124 := by
  refine rwStatement_of_inst 124 ?_
  intro S' e f hS he hef hcop hN
  push_cast at hN
  have hd : f ^ 2 + 2 * f - 1 ≤ 2 * f ^ 2 - e ^ 2 := by nlinarith
  have hS4 : 4 ≤ S' ^ 2 := by nlinarith
  have hf2 : 2 ≤ f := by omega
  have hf : f ≤ 5 := by nlinarith
  have hS5 : S' ≤ 4 := by
    by_contra h; push_neg at h
    have : 25 ≤ S' ^ 2 := by nlinarith
    nlinarith
  interval_cases S' <;> interval_cases f <;> interval_cases e <;>
    first | (norm_num at hN; done) | exact @s4inst_2_1_4

theorem arith : ∀ M M' : ℤ, 0 < M → 0 < M' → ((124 : ℕ) : ℤ) = M * M' → (2 : ℤ) ∣ M - ((124 : ℕ) : ℤ) →
    (2 : ℤ) ∣ M' - ((124 : ℕ) : ℤ) → 3 * M < M' → M = 2 ∧ M' = 2 * (2 * ((15 : ℕ) : ℤ) + 1) := by
  intro M M' hM hM' hN h1 h2 h3
  push_cast at *
  have : M ≤ 8 := by nlinarith
  interval_cases M <;> omega

/-- `CaseGClosed 124` (`γ = 2α`). -/
theorem caseG : CaseGClosed 124 := Erdos634.GLK.caseG_of_leafOnly 124 15 (by norm_num) arith

/-- **`124` is not a tile count** (no `CongruentDissection 124` exists). -/
theorem not_tile_124 (D : CongruentDissection 124) : False :=
  not_tile_of_leaves 124 (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (gapE60_of_chk' (by norm_num) (by decide +kernel)) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    rw124 ra caseG
    (gapE120_of_chk (by norm_num) (by decide +kernel)) D

end Erdos634.Draft.N124

#print axioms Erdos634.Draft.N124.not_tile_124
