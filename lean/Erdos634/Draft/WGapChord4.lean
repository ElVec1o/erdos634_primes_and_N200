/-
Draft/WGapChord4.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 chord facts (C)).
Not imported by any aggregate.  Module W6a: `chain_edge_len_a`: EVERY chain edge inside a clamped run of length `j a` (`1 ≤ j ≤ f-1`) is an `a`-edge
(FINDINGS F8: used to kill the c-edge alternative of `w1_fill`).  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapChord3

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

section chord4

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **Every chain edge inside a clamped run of length `j a` is an `a`-edge** (`1 ≤ j ≤ f - 1`). -/
theorem chain_edge_len_a (S : SetupG D e f α β γ L ax ay) {j : ℕ} (hj1 : 1 ≤ j) (hjf : j ≤ f - 1)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q P' Q' : Plane} (hPQ : P ≠ Q)
    (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P Q)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Q P)
    (hd : dist P Q = (j : ℝ) * ((e : ℝ) * f))
    {e0 : Fin N × Fin 3} (he0 : e0 ∈ D.lineChain F c)
    (hsub : (D.tile e0.1).edge e0.2 ⊆ segment ℝ P Q) :
    dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) = (e : ℝ) * f := by
  have hS := Erdos634.RunPartition.CSlot.segment_subset_level F c hfP hfQ
  obtain ⟨x, y, z, hxyz⟩ :=
    wall_partitionG D S.hM F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ he0 hsub
  rw [hd] at hxyz
  exact first_len_jaG S.he S.hef S.hco hj1 hjf (edge_length_casesG D S.hM e0.1 e0.2) hxyz

end chord4

#print axioms chain_edge_len_a

end Erdos634.Draft.WGapStmt
