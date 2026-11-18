/-
Draft/WGapClimb6.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.3 at `h = 0 = i - lambda`).
Not imported by any aggregate.  No sorry, no native_decide.
* `climb_end0`: `ClimbSt ... i` (the climb has reached `lambda = i`), `Pi4` and `j + i >= 1` give `False`: at `A_0 = p(0, j+i+1)` the strip tile, `U(0, j+i)`, `N^0` leave one beta wedge (`rl_A0_fill`), which is `(r3)` at `t = 0`; then `rl_nat`.
-/
import Erdos634.Draft.WGapClimb5

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

section climb6

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 32000000 in
theorem climb_end0 (S : SetupG D e f α β γ L ax ay) {c₀ J j i : ℕ} (hJ : J ≤ j + i) (hij : i + j + 1 ≤ f - 1)
    (hj1 : 1 ≤ j + i) (hSt : ClimbSt D e f c₀ J j i i) (hP4 : Pi4 D e f c₀ i j) : False := by
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hSt
  obtain ⟨J1, hJ1⟩ : ∃ J1, j + i = J1 + 1 := ⟨j + i - 1, by omega⟩
  have hy : ((j + i : ℕ) : ℝ) = (J1 : ℝ) + 1 := by exact_mod_cast hJ1
  obtain ⟨tE, hEt⟩ := hS1 (j + i) (by omega) (by omega)
  obtain ⟨tUi, hUit⟩ := hUa 0 (j + i) (by omega) (by omega)
  have hN0 := hC1 0 (by omega) (by omega)
  rw [Nat.sub_zero] at hN0
  obtain ⟨tN0, hN0t⟩ := hN0
  rw [hy] at hEt hUit hN0t
  have hleft := rl_A0_fill S (xo f c₀) J1 hEt (hv hUit) (hv hN0t)
  have hPIR : ∀ t m : ℝ, PIR (e : ℝ) f (xo f c₀) J1 1 t m = PIR (e : ℝ) f (xo f c₀) j i t m := by
    intro t m
    unfold PIR
    refine lpG_congr rfl ?_
    have h : ((j : ℝ) + i) = (J1 : ℝ) + 1 := by exact_mod_cast hJ1
    push_cast
    linarith
  simp only [hPIR] at hleft
  refine rl_nat S c₀ j i 0 (by omega) (by omega) ?_ ?_ ?_ hP4 ?_
  · intro t' h1 h2'
    exact hC1 t' (by omega) h2'
  · intro t' h1 h2'
    exact hUa t' (j + i - t') (by omega) (by omega)
  · intro t' h1 h2'
    exact hDa (t' - 1) (j + i - t') (by omega) (by omega)
  · obtain ⟨F, R, lamc, hl, hF, hR⟩ := hleft
    exact ⟨F, R, lamc, hl, hF, hR⟩

end climb6

#print axioms climb_end0

end Erdos634.Draft.WGapStmt
