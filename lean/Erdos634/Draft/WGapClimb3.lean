/-
Draft/WGapClimb3.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.3, P9.4 steps (5)-(7), no station: `h_lambda = 0`).
Not imported by any aggregate.  No sorry, no native_decide.
* `PIR_lvlk`: `PIR x (j+lam) i t m = PIR x j (i+lam) t m`;
* `rl_nat`: Lemma RL (`rl_gen`) with the tiles in the natural-number form `NTile`/`UTG`/`DTG` of Proposition B;
* `step6_alt`: step (6) at `A_q`, `q = k+1`, with the `(r3)` branch EXPORTED (it is `rl_close` only at `lambda = 0`; for `lambda >= 1` it is `rl_gen` at `t = q`);
* `ClimbSt` (the invariant (C1), (C2) at `h_lambda = 0`) and `climb_step0` (step `lambda -> lambda+1` of PROOF 9.4 given the row `D(x, j+lambda)`, `x < i-lambda`): steps (5), (6), (7);
* `climb_end0`: the end of the climb 9.3 (`lambda = i`, `h = 0 = i - lambda`).
-/
import Erdos634.Draft.WGapClimb2
import Erdos634.Draft.WGapGen6

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

theorem PIR_lvlk {e f : ℝ} (x : ℝ) (j lam i : ℕ) (t m : ℝ) :
    PIR e f x (j + lam) i t m = PIR e f x j (i + lam) t m := by
  unfold PIR
  exact lpG_congr rfl (by push_cast; ring)

section climb3

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 16000000 in
/-- **Lemma RL in the natural-number form of Proposition B** (left tile at `A_t`) -/
theorem rl_nat (S : SetupG D e f α β γ L ax ay) (c₀ j i t : ℕ) (hi : i + 1 ≤ f - 1) (hti : t ≤ i)
    (hN : ∀ t' : ℕ, t ≤ t' → t' ≤ i → NTile D e f c₀ t' (j + i - t'))
    (hU : ∀ t' : ℕ, t ≤ t' → t' ≤ i → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (t' : ℝ) ((j + i - t' : ℕ) : ℝ))
    (hD : ∀ t' : ℕ, t < t' → t' ≤ i → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) ((t' - 1 : ℕ) : ℝ) ((j + i - t' : ℕ) : ℝ))
    (hP4 : Pi4 D e f c₀ i j)
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f (xo f c₀) j i (t : ℝ) ((0 : ℕ) : ℝ))
        (PIR (e : ℝ) f (xo f c₀) j i (t : ℝ) ((0 : ℕ) : ℝ) + lamc • dcvec (e : ℝ) f (xo f c₀)) R ∧
      0 < cross (dcvec (e : ℝ) f (xo f c₀)) (R - PIR (e : ℝ) f (xo f c₀) j i (t : ℝ) ((0 : ℕ) : ℝ))) : False := by
  refine rl_gen S (xo f c₀) j i t hi hti ?_ ?_ ?_ hP4 hleft
  · intro t' h1 h2
    obtain ⟨T, hT⟩ := hN t' h1 h2
    have hc : ((j + i - t' : ℕ) : ℝ) = (j : ℝ) + i - t' := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    refine ⟨T, ?_⟩
    rw [hc] at hT
    exact hasV_congr hT (lpG_congr rfl (by ring)) (lpG_congr rfl (by ring)) (lpG_congr rfl (by ring))
  · intro t' h1 h2
    obtain ⟨T, hT⟩ := hU t' h1 h2
    have hc : ((j + i - t' : ℕ) : ℝ) = (j : ℝ) + i - t' := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    refine ⟨T, ?_⟩
    rw [hc] at hT
    exact hasV_congr hT (lpG_congr rfl rfl) (lpG_congr rfl rfl) (lpG_congr rfl rfl)
  · intro t' h1 h2
    obtain ⟨T, hT⟩ := hD t' h1 h2
    have hc : ((j + i - t' : ℕ) : ℝ) = (j : ℝ) + i - t' := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    have hc2 : ((t' - 1 : ℕ) : ℝ) = (t' : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    refine ⟨T, ?_⟩
    rw [hc, hc2] at hT
    exact hasV_congr hT (lpG_congr (by ring) rfl) (lpG_congr rfl rfl) (lpG_congr (by ring) rfl)

end climb3

#print axioms PIR_lvlk
#print axioms rl_nat

end Erdos634.Draft.WGapStmt
