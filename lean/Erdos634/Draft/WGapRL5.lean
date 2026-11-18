/-
Draft/WGapRL5.lean -- written 16 November 2026 (session 9).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P8.2, "Case tau = i - m": Xi = Z impossible).
Not imported by any aggregate.  `rl_close`: when the top point `C_m = pi(tau, m+1)` of (beta) is the bottom point `B_m = pi(i-m, m+1)` of (alpha) (`tau + m = i`), the two half-disk covers
(on the right of `Lambda_3`, on the left of `L^(tau)`) clash (`edgecover_clash`, `cross (Y-O) w = -kapG != 0`): False.  This ENDS the RL recursion.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapRL4

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

section rl5

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem rl_close (S : SetupG D e f α β γ L ax ay) (x : ℝ) (j i τ μ0 m : ℕ) (hμ : μ0 ≤ m) (hm : m ≤ i) (hi : i + 1 ≤ f - 1)
    (hτ : τ + m = i)
    (hnuA : ∀ m' : ℕ, m' ≤ m → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((i : ℝ) - m' + 1) m') (PIR (e : ℝ) f x j i ((i : ℝ) - m') m')
        (PIR (e : ℝ) f x j i ((i : ℝ) - m') ((m' : ℝ) + 1)))
    (hP4 : ∃ (F : Fin N) (R : Plane),
      HasV D F (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + nuG (e : ℝ) f •
          (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)) R ∧
      cross (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j)
        (R - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) < 0)
    (hnuB : ∀ m' : ℕ, μ0 ≤ m' → m' ≤ m → ∃ T : Fin N,
      HasV D T (PIR (e : ℝ) f x j i ((τ : ℝ) + 1) m') (PIR (e : ℝ) f x j i τ m') (PIR (e : ℝ) f x j i τ ((m' : ℝ) + 1)))
    (hleft : ∃ (F : Fin N) (R : Plane) (lamc : ℝ), (lamc = (e : ℝ) / f ∨ lamc = 1) ∧
      HasV D F (PIR (e : ℝ) f x j i τ μ0) (PIR (e : ℝ) f x j i τ μ0 + lamc • dcvec (e : ℝ) f x) R ∧
      0 < cross (dcvec (e : ℝ) f x) (R - PIR (e : ℝ) f x j i τ μ0)) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have A := rl_alpha S x j i m hi hm hnuA hP4
  have B := rl_beta S x j i τ μ0 m hμ hm hi hnuB hleft
  have hτR : (τ : ℝ) = (i : ℝ) - m := by
    have : (τ : ℝ) + m = i := by exact_mod_cast hτ
    linarith
  have hpt : PIR (e : ℝ) f x j i (τ : ℝ) ((m : ℝ) + 1) = lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j + (((m + 1 : ℕ) : ℝ)) •
      (lpG (e : ℝ) f 1 x ((i : ℝ) - nuG (e : ℝ) f) ((j : ℝ) + 2 + nuG (e : ℝ) f) - lpG (e : ℝ) f 1 x ((i : ℝ) + 1) j) := by
    rw [show (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 by push_cast; ring]
    exact PIR_on_L3 he0 hef x j i _ _ (by rw [hτR]; ring)
  rw [hpt] at B
  have hK := rl_cross_ne he0 hef x (i : ℝ) (j : ℝ)
  exact edgecover_clash (Or.inr rfl) (Or.inl rfl) (by rw [hK]; exact neg_ne_zero.mpr (kapG_pos he0 hef).ne') A B

end rl5

#print axioms rl_close
#print axioms rl_alpha
#print axioms rl_beta
#print axioms fault_cover
#print axioms edgecover_clash

end Erdos634.Draft.WGapStmt
