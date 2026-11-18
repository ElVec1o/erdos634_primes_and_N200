/-
Draft/WGapRL7.lean -- written 16 November 2026 (session 10).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, the wedge fill of Gamma_{t'} at every layer m).
Not imported by any aggregate.  No sorry, no native_decide.
`rl_fill_gen`: the ABSTRACT five-tile wedge fill at a point `O` (no lattice coordinates): known tiles `G1` (alpha), `G2` (gamma), `G3` (beta) below, `N2` (gamma), `N` (beta) above,
`N` with vertices `O, Y, Z` (`Z` left of `O -> Y`), the four others with no vertex on the open ray `O -> Y`, `G2 != N2`, `G3 != N`.  The free wedge has size `alpha`, so the tile next to the ray is an
`alpha`-tile `tau` with vertices `O, P, W` (`P` on the open ray, `W` on the right, `|PW| = a`, `{|OP|,|OW|} = {b,c}`).  Used for layer m = 0 (`rl_gamma_fill`) and m >= 1 (reflected lattice).
-/
import Erdos634.Draft.WGapRL6

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

section rl7

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem rl_fill_gen (S : SetupG D e f α β γ L ax ay) {O Y Z : Plane} {tG1 tG2 tG3 tN2 tN : Fin N}
    (aG1 : (D.tile tG1).localAngle O = α) (aG2 : (D.tile tG2).localAngle O = γ) (aG3 : (D.tile tG3).localAngle O = β)
    (aN2 : (D.tile tN2).localAngle O = γ) (aN : (D.tile tN).localAngle O = β)
    (nG2N2 : tG2 ≠ tN2) (nG3N : tG3 ≠ tN)
    (hN : HasV D tN O Y Z) (hZ : 0 < cross (Y - O) (Z - O)) (hXY : O ≠ Y)
    (rG1 : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tG1).pts j ≠ AffineMap.lineMap O Y s)
    (rG2 : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tG2).pts j ≠ AffineMap.lineMap O Y s)
    (rG3 : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tG3).pts j ≠ AffineMap.lineMap O Y s)
    (rN2 : ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile tN2).pts j ≠ AffineMap.lineMap O Y s) :
    ∃ τ : Fin N, ∃ P W : Plane, HasV D τ O P W ∧ (∃ s : ℝ, 0 < s ∧ P = AffineMap.lineMap O Y s) ∧
      cross (Y - O) (W - O) < 0 ∧ (D.tile τ).localAngle O = α ∧ dist P W = (e : ℝ) * f ∧
      ((dist O P = (f : ℝ) ^ 2 ∧ dist O W = (f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∨
        (dist O P = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist O W = (f : ℝ) ^ 2)) := by
  have hA := S.hA
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have n12 : tG1 ≠ tG2 := ne_of_angle (by rw [aG1, aG2]; exact hαγ)
  have n13 : tG1 ≠ tG3 := ne_of_angle (by rw [aG1, aG3]; exact hαβ)
  have n14 : tG1 ≠ tN2 := ne_of_angle (by rw [aG1, aN2]; exact hαγ)
  have n15 : tG1 ≠ tN := ne_of_angle (by rw [aG1, aN]; exact hαβ)
  have n23 : tG2 ≠ tG3 := ne_of_angle (by rw [aG2, aG3]; exact hβγ.symm)
  have n24 : tG2 ≠ tN2 := nG2N2
  have n25 : tG2 ≠ tN := ne_of_angle (by rw [aG2, aN]; exact hβγ.symm)
  have n34 : tG3 ≠ tN2 := ne_of_angle (by rw [aG3, aN2]; exact hβγ)
  have n35 : tG3 ≠ tN := nG3N
  have n45 : tN2 ≠ tN := ne_of_angle (by rw [aN2, aN]; exact hβγ.symm)
  have hOint : O ∈ interior D.target.carrier := by
    refine interior_of_four D n12 n14 n15 n24 n25 n45 ?_
    rw [aG1, aG2, aN2, aN]
    have hr := hA.hrel
    have hg := hA.hγdef
    have h1 := hA.hα
    have h2 := hA.hβ
    linarith
  set K : Finset (Fin N) := {tG1, tG2, tG3, tN2, tN} with hKdef
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle O = 2 * Real.pi - α := by
    rw [hKdef, sum_five _ n12 n13 n14 n15 n23 n24 n25 n34 n35 n45, aG1, aG2, aG3, aN2, aN]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  have hΩ : ∑ i, (D.tile i).localAngle O = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq O
    rw [this, D.target.localAngle_interior hOint]
  have hYt : Y ∈ D.target.carrier := hN.mem₂
  have hint := openSeg_interior D.toDissection hOint hYt
  have hP' : cross (Y - O) ((O - (Y - O)) - O) = 0 := by
    simp [cross]; ring
  have hXP : O ∈ openSegment ℝ (O - (Y - O)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle O < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · rw [aG1]; exact hαπ
    · rw [aG2]; exact hγπ
    · rw [aG3]; exact hβπ
    · rw [aN2]; exact hγπ
    · rw [aN]; exact hβπ
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) hKsum hαπ hKlt
  have hKray : ∀ k ∈ K, k ≠ tN → ∀ (j : Fin 3) (s : ℝ), 0 < s → (D.tile k).pts j ≠ AffineMap.lineMap O Y s := by
    intro k hk hkt
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl
    · exact rG1
    · exact rG2
    · exact rG3
    · exact rN2
    · exact absurd rfl hkt
  obtain ⟨τ, -, P, W, h⟩ := filler_alpha S hXY hN hZ hP' hXP hint hclamp hΩ K hKsum hKray
  exact ⟨τ, P, W, h⟩

end rl7

end Erdos634.Draft.WGapStmt
