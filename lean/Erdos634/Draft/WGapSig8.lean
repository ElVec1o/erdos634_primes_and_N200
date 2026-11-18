/-
Draft/WGapSig8.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b2)).
Not imported by any aggregate.  No sorry, no native_decide.
`no_five_bg`: five distinct tiles at an INTERIOR vertex of the target, each showing `β` or `γ`, cannot exist (every vertex figure has `b + g ≤ 4`; `fig_int`).
-/
import Erdos634.Draft.WGapSig7

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapStmt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

variable {N : ℕ} {D : CongruentDissection N}

section sig8

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem no_five_bg (S : SetupG D e f α β γ L ax ay) {v : Plane} (hv : v ∈ interior D.target.carrier)
    {j : Fin N} {m : Fin 3} (hjm : (D.tile j).pts m = v) (F : Finset (Fin N)) (hF : 5 ≤ F.card)
    (hang : ∀ i ∈ F, (D.tile i).localAngle v = β ∨ (D.tile i).localAngle v = γ) : False := by
  have fig := fig_int S hv hjm
  unfold FigI at fig
  have hsub : F ⊆ ({i | (D.tile i).localAngle v = β} : Finset (Fin N)) ∪ ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)) := by
    intro i hi
    rcases hang i hi with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
  have hdisj : Disjoint ({i | (D.tile i).localAngle v = β} : Finset (Fin N)) ({i | (D.tile i).localAngle v = γ} : Finset (Fin N)) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    rw [Finset.mem_filter] at h1 h2
    have hβγ : β ≠ γ := by
      have := S.hA
      have hg := this.hγdef
      have hb := this.hβ
      have ha := this.hα
      intro h; linarith
    exact hβγ (h1.2.symm.trans h2.2)
  have hc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj] at hc
  omega

end sig8

#print axioms no_five_bg

end Erdos634.Draft.WGapStmt
