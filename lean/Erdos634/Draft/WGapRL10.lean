/-
Draft/WGapRL10.lean -- written 16 November 2026 (session 11).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2: the wedge fill at `B_m`, size `beta`).
Not imported by any aggregate.  No sorry, no native_decide.
* `rl_beta_fill_abs`: abstract `beta`-wedge fill at `X`: a `gamma`-tile `tG` with vertices `(X, Y, Z)` (left of the ray `X -> Y`), an `alpha`-tile `tN` at `X` (no vertex on the open ray), and a half-disk cover
  `EdgeCoverS D X d (-1)` of the right of the line `d` (with `Y` strictly left of `d`) leave a wedge `beta`; the tile beside the ray is a `beta`-tile (vertices `X`, `P` on the ray, `W` right of the ray, `|PW| = b`, `{|XP|,|XW|} = {a,c}`).
-/
import Erdos634.Draft.WGapRL9
import Erdos634.Draft.WGapStSide

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

section rl10

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem rl_beta_fill_abs (S : SetupG D e f α β γ L ax ay) {X Y Z d : Plane} {tG tN : Fin N}
    (hXY : X ≠ Y) (hG : HasV D tG X Y Z) (hZ : 0 < cross (Y - X) (Z - X))
    (aG : (D.tile tG).localAngle X = γ) (aN : (D.tile tN).localAngle X = α)
    (hΞ : EdgeCoverS D X d (-1)) (hcr : 0 < cross d (Y - X))
    (hNray : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tN).pts j ≠ AffineMap.lineMap X Y s) :
    ∃ τ : Fin N, ∃ P W : Plane, HasV D τ X P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap X Y s) ∧
      cross (Y - X) (W - X) < 0 ∧ (D.tile τ).localAngle X = β ∧ dist P W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧
      ((dist X P = (e : ℝ) * f ∧ dist X W = (f : ℝ) ^ 2) ∨
        (dist X P = (f : ℝ) ^ 2 ∧ dist X W = (e : ℝ) * f)) := by
  obtain ⟨φ, hφX, hφang, hφpush⟩ := hΞ
  have hA := S.hA
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have hGN : tG ≠ tN := ne_of_angle (by rw [aG, aN]; exact hαγ.symm)
  have hφG : φ ≠ tG := ne_of_angle (by rw [hφang, aG]; exact hγπ.ne')
  have hφN : φ ≠ tN := ne_of_angle (by rw [hφang, aN]; exact hαπ.ne')
  set K : Finset (Fin N) := {tG, tN, φ} with hKdef
  have hXt : X ∈ D.target.carrier := hG.mem₁
  have hYt : Y ∈ D.target.carrier := hG.mem₂
  have hKsum3 : ∑ i ∈ K, (D.tile i).localAngle X = γ + α + Real.pi := by
    rw [hKdef, Finset.sum_insert (by simp [hGN, hφG.symm]), Finset.sum_insert (by simp [hφN.symm]),
      Finset.sum_singleton, aG, aN, hφang]
    ring
  have hr := hA.hrel
  have hg := hA.hγdef
  have h1 := hA.hα
  have h2 := hA.hβ
  have hXint : X ∈ interior D.target.carrier := by
    refine interior_of_sum D.toDissection hXt K ?_
    rw [hKsum3]; linarith
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle X = 2 * Real.pi - β := by
    rw [hKsum3]; linarith
  have hΩ : ∑ i, (D.tile i).localAngle X = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq X
    rw [this, D.target.localAngle_interior hXint]
  obtain ⟨hα0, -, hγ0⟩ := wedge_beta S hΩ hKsum hβπ
  have hint := openSeg_interior D.toDissection hXint hYt
  have hP' : cross (Y - X) ((X - (Y - X)) - X) = 0 := by
    simp [cross]; ring
  have hXP : X ∈ openSegment ℝ (X - (Y - X)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hw : 0 < -1 * cross d ((X - (Y - X)) - X) := by
    have : -1 * cross d ((X - (Y - X)) - X) = cross d (Y - X) := by simp [cross]; ring
    rw [this]; exact hcr
  obtain ⟨ε0, hε0, hp⟩ := hφpush _ hw
  have hclamp : ∀ ed ∈ D.lineChain (crossL (Y - X)) (cross (Y - X) X),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (X - (Y - X)) X Y := by
    intro ed _
    refine not_straddles_short D.toDissection (P' := X - (Y - X)) (P := X) (Q := Y) (δ := ε0) (ρ := 1) hε0
      one_pos ?_ (fun ε hε hεδ => hp ε hε hεδ) ed.1 ed.2
    ext i; simp
  have hpush' : ∀ w : Plane, 0 < cross (-d) w → ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε' : ℝ, 0 < ε' → ε' < ε₀ →
      X + ε' • w ∈ interior (D.tile φ).carrier := by
    intro w hw'
    refine hφpush w ?_
    have : cross (-d) w = -cross d w := by simp [cross]; ring
    linarith
  have hWh := Erdos634.Draft.WGapSt.edgeCover_halfplane φ hφang hpush'
  have hKray : ∀ k ∈ K, k ≠ tG → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap X Y s := by
    intro k hk hkt j s hs hv
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl
    · exact absurd rfl hkt
    · exact hNray j s hs hv
    · have hmem : (D.tile k).pts j ∈ (D.tile k).carrier := subset_convexHull ℝ _ ⟨j, rfl⟩
      have h0' := hWh _ hmem
      rw [hv] at h0'
      have e2 : cross (-d) (AffineMap.lineMap X Y s - X) = -(s * cross d (Y - X)) := by
        rw [AffineMap.lineMap_apply]; simp [cross]; ring
      rw [e2] at h0'
      nlinarith [mul_pos hs hcr]
  obtain ⟨τ, -, P, W, hV, hPray, hW, hang, hPW, hsides⟩ :=
    filler_beta S hXY hG hZ hP' hXP hint hclamp K hα0 hγ0 hKray
  exact ⟨τ, P, W, hV, hPray, hW, hang, hPW, hsides⟩

end rl10

#print axioms rl_beta_fill_abs

end Erdos634.Draft.WGapStmt
