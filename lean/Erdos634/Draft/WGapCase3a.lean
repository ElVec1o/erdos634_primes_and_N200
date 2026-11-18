/-
Draft/WGapCase3a.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 Case 3, (A1) with multiplier m <= f-1).
Not imported by any aggregate.  Module P-D2: `chain_edge_len_b`: EVERY chain edge inside a clamped run of length `m b` (`1 <= m <= f-1`) is a `b`-edge (copy of `chain_edge_len_a` with `first_len_jbG`).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapSide3d

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

section case3a

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **Every chain edge inside a clamped run of length `m b` is a `b`-edge** (`1 ≤ m ≤ f - 1`). -/
theorem chain_edge_len_b (S : SetupG D e f α β γ L ax ay) {m : ℕ} (hm1 : 1 ≤ m) (hmf : m ≤ f - 1)
    (F : Plane →ₗ[ℝ] ℝ) (hF : F ≠ 0) (c : ℝ) {P Q P' Q' : Plane} (hPQ : P ≠ Q)
    (hfP : F P = c) (hfQ : F Q = c) (hfP' : F P' = c) (hfQ' : F Q' = c)
    (hP' : P ∈ openSegment ℝ P' Q) (hQ' : Q ∈ openSegment ℝ P Q')
    (hint : openSegment ℝ P Q ⊆ interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ P Q, ∀ i, y ∉ interior (D.tile i).carrier)
    (hP : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) P' P Q)
    (hQ : ∀ ed ∈ D.lineChain F c, ¬ Straddles ((D.tile ed.1).edge ed.2) Q' Q P)
    (hd : dist P Q = (m : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    {e0 : Fin N × Fin 3} (he0 : e0 ∈ D.lineChain F c)
    (hsub : (D.tile e0.1).edge e0.2 ⊆ segment ℝ P Q) :
    dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  have hS := Erdos634.RunPartition.CSlot.segment_subset_level F c hfP hfQ
  obtain ⟨x, y, z, hxyz⟩ :=
    wall_partitionG D S.hM F hF c hPQ hfP' hfQ' hP' hQ' hS hint hwall hP hQ he0 hsub
  rw [hd] at hxyz
  exact first_len_jbG S.he S.hef S.hco hm1 hmf (edge_length_casesG D S.hM e0.1 e0.2) hxyz

end case3a

#print axioms chain_edge_len_b

end Erdos634.Draft.WGapStmt
