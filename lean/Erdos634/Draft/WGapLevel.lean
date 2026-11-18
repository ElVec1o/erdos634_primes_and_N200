/-
Draft/WGapLevel.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 step j -> j+1: far half-plane wedge at the inner chord points).
Not imported by any aggregate.  Module W8b: `level_fill`: at level `η` (the proof's `j`), with the chord hypotheses of `chord_D_all`, at every inner chord point `p'(i, η-i)`, `1 ≤ i < n`,
the `α`-wedge `(α, 2α)` is filled by `U'(i, η-i)` or by the flipped tile (`w2_fill` with the five known tiles: `NearOK` and `D'(i-1,η-i)`, `D'(i,η-i-1)` from `chord_D_all`).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapChordHyps

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

section level

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
theorem level_fill (S : SetupG D e f α β γ L ax ay) (x η : ℝ)
    (hU0 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 1 η) (lpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 η) (mpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 (η - 1)) (mpG (e : ℝ) f 1 x 0 (η - 1)))
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 0 (η - 1)) (lpG (e : ℝ) f 1 x 1 (η - 1)))
    {n : ℕ} (hn1 : 1 ≤ n) (hnf : n ≤ f - 1)
    (hint : openSegment ℝ (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)) ⊆
        interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)),
        ∀ i, y ∉ interior (D.tile i).carrier)
    (hEc : ∀ ed ∈ D.lineChain (crossL (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (cross (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 0 η)),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 x 0 η + ((n : ℝ) + 1) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η))
    (hnear : ∀ i : ℕ, 1 ≤ i → i < n → NearOK D (e : ℝ) f x (i : ℝ) (η - (i : ℝ))) :
    ∀ i : ℕ, 1 ≤ i → i < n →
      (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) (η - (i : ℝ))) (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η - (i : ℝ)))
        (mpG (e : ℝ) f 1 x (i : ℝ) (η - (i : ℝ) + 1))) ∨
      (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) (η - (i : ℝ)))
        (mpG (e : ℝ) f 1 x ((i : ℝ) + nuG (e : ℝ) f) (η - (i : ℝ)))
        (mpG (e : ℝ) f 1 x (i : ℝ) (η - (i : ℝ) + 1 / nuG (e : ℝ) f))) := by
  have hD := chord_D_all S x η hU0 hT hT1 hU1 hn1 hnf hint hwall hEc hnear
  intro i hi1 hin
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  obtain ⟨hn1', hn2', hn3'⟩ := hnear (i' + 1) (by omega) hin
  obtain ⟨τa, hτa⟩ := hD i' (by omega)
  obtain ⟨τb, hτb⟩ := hD (i' + 1) hin
  refine w2_fill S x ((i' + 1 : ℕ) : ℝ) (η - ((i' + 1 : ℕ) : ℝ)) hn1' hn2' hn3' ?_ ?_
  · refine ⟨τa, hasV_congr hτa.swap ?_ ?_ ?_⟩ <;> exact mpG_congr' (by push_cast; ring) (by push_cast; ring)
  · refine ⟨τb, hasV_congr hτb.rot.rot.swap ?_ ?_ ?_⟩ <;> exact mpG_congr' (by push_cast; ring) (by push_cast; ring)

end level

#print axioms level_fill

end Erdos634.Draft.WGapStmt
