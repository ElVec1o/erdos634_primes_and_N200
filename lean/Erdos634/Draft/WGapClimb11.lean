/-
Draft/WGapClimb11.lean -- written 16 November 2026 (session 16).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P9.4 (3a), first alternative).
Not imported by any aggregate.  No sorry, no native_decide.
* `station_Pi4_false`: if the tile `F_k` in the wedge `(2α,3α)` at the station candidate `O = p(x+1, j+lam)` lays `b` on the chord of `N_x(j+lam)` (this is `Pi4 D e f c₀ x (j+lam)`), then `Pi_b^𝔞(j+lam, x)` occurs, contradicting `BUpTo` (index `x <= i - lam - 2 < i - 1`).  This is the first alternative of (3a); the second (`F_k` lays `c`, `b` on `L_O`) is `St2` at `O`.
-/
import Erdos634.Draft.WGapClimb10

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

section climb11

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem station_Pi4_false {c₀ J j i lam x : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ j + lam) (hij : i + j + 1 ≤ f - 1)
    (hlt : lam < i) (hSt : ClimbSt D e f c₀ J j i lam) (hB : BUpTo D e f (i - 1)) (hx2 : x + 2 + lam ≤ i)
    (hbefore : ∀ x' : ℕ, x' < x → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) (x' : ℝ) ((j + lam : ℕ) : ℝ))
    (hN : NTile D e f c₀ x (j + lam)) (hPi4 : Pi4 D e f c₀ x (j + lam)) : False := by
  obtain ⟨hC1, hS1, hUa, hDa⟩ := hSt
  exact hB c₀ J hA (j + lam) x hJ (by omega) (by omega)
    ⟨hS1, fun a b hb hab => hUa a b hb (by omega), fun a b hb hab => hDa a b hb (by omega), hbefore, hN, hPi4⟩

end climb11

#print axioms station_Pi4_false

end Erdos634.Draft.WGapStmt
