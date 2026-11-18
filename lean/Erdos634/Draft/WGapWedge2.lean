/-
Draft/WGapWedge2.lean -- written 15 November 2026.  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15.
Not imported by any aggregate.  Module W3b: the wedge API, part A, one corollary per wedge size of WEDGE_USES.md (via `WGapAngles.fill_*`).

`cnt D K X v` = number of tiles outside `K` whose local angle at `X` is `v`.  Each corollary has the hypotheses of `wedge_count`
(`∑ localAngle = Ω`, `∑_K = Ω - θ`, `θ < π`) with `θ` the wedge, and concludes the exact filling:
  `wedge_alpha` (W2,W3,W6: one `α`), `wedge_beta` (W1,W9: one `β`), `wedge_alpha_beta` (W10), `wedge_2alpha` (W5), `wedge_3alpha` (W11),
  `wedge_gamma` (W4,W7: one `γ`, or `{α,α,β}`), `wedge_pi_sub_beta` (W8: `{α,α,α,β}` or `{α,γ}`).
Witness/negative control: `wedge_alpha_not_beta`: a wedge of size `α` is never filled by a `β` tile (the ledger excludes it).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapWedge

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

/-- number of tiles outside `K` whose local angle at `X` is `v` -/
noncomputable def cnt (D : CongruentDissection N) (K : Finset (Fin N)) (X : Plane) (v : ℝ) : ℕ :=
  ((Finset.univ \ K).filter (fun i => (D.tile i).localAngle X = v)).card

section cor

variable {e f : ℕ} {α β γ L ax ay : ℝ} {X : Plane} {Ω θ : ℝ} {K : Finset (Fin N)}

theorem wedge_alpha (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - α) (hθπ : α < Real.pi) :
    cnt D K X α = 1 ∧ cnt D K X β = 0 ∧ cnt D K X γ = 0 := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK hθπ
  have := Erdos634.Draft.WGapAngles.fill_alpha S.hA h
  unfold cnt; omega

theorem wedge_beta (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - β) (hθπ : β < Real.pi) :
    cnt D K X α = 0 ∧ cnt D K X β = 1 ∧ cnt D K X γ = 0 := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK hθπ
  have := Erdos634.Draft.WGapAngles.fill_beta S.hA h
  unfold cnt; omega

theorem wedge_alpha_beta (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - (α + β)) (hθπ : α + β < Real.pi) :
    cnt D K X α = 1 ∧ cnt D K X β = 1 ∧ cnt D K X γ = 0 := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK hθπ
  have := Erdos634.Draft.WGapAngles.fill_alpha_beta S.hA h
  unfold cnt; omega

theorem wedge_2alpha (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - 2 * α) (hθπ : 2 * α < Real.pi) :
    cnt D K X α = 2 ∧ cnt D K X β = 0 ∧ cnt D K X γ = 0 := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK hθπ
  have := Erdos634.Draft.WGapAngles.fill_2alpha S.hA h
  unfold cnt; omega

theorem wedge_3alpha (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - 3 * α) (hθπ : 3 * α < Real.pi) :
    cnt D K X α = 3 ∧ cnt D K X β = 0 ∧ cnt D K X γ = 0 := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK hθπ
  have := Erdos634.Draft.WGapAngles.fill_3alpha S.hA h
  unfold cnt; omega

theorem wedge_gamma (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - γ) (hθπ : γ < Real.pi) :
    (cnt D K X α = 0 ∧ cnt D K X β = 0 ∧ cnt D K X γ = 1) ∨
      (cnt D K X α = 2 ∧ cnt D K X β = 1 ∧ cnt D K X γ = 0) := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK hθπ
  have := Erdos634.Draft.WGapAngles.fill_gamma S.hA h
  unfold cnt; omega

theorem wedge_pi_sub_beta (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - (Real.pi - β)) (hθπ : Real.pi - β < Real.pi) :
    (cnt D K X α = 3 ∧ cnt D K X β = 1 ∧ cnt D K X γ = 0) ∨
      (cnt D K X α = 1 ∧ cnt D K X β = 0 ∧ cnt D K X γ = 1) := by
  obtain ⟨x, y, z, h, hx, hy, hz, -⟩ := wedge_count S hΩ K hK hθπ
  have := Erdos634.Draft.WGapAngles.fill_pi_sub_beta S.hA h
  unfold cnt; omega

/-- the angle `α < π`, `β < π`, ... facts for the corollaries' last hypothesis -/
theorem angles_lt_pi (S : SetupG D e f α β γ L ax ay) :
    α < Real.pi ∧ β < Real.pi ∧ γ < Real.pi ∧ 2 * α < Real.pi ∧ 3 * α < Real.pi ∧ α + β < Real.pi := by
  have hA := S.hA
  obtain ⟨h0, hb0, hag, hbg, h2g, hgb, hgp, hhalf⟩ := Erdos634.Draft.WGapAngles.angle_ineqs hA
  have hr := hA.hrel
  have hpi := Real.pi_pos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- negative control: a wedge of size `α` is never filled by a `β` tile -/
theorem wedge_alpha_not_beta (S : SetupG D e f α β γ L ax ay) (hΩ : ∑ i, (D.tile i).localAngle X = Ω)
    (hK : ∑ i ∈ K, (D.tile i).localAngle X = Ω - α) (hθπ : α < Real.pi) :
    ¬ 0 < cnt D K X β := by
  have := (wedge_alpha S hΩ hK hθπ).2.1
  omega

end cor

end Erdos634.Draft.WGapStmt
