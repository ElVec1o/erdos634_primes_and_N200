/-
Draft/WGapU3.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 Lemma U3), corrected statement S2' (FINDINGS F11).
Not imported by any aggregate.  Module P-E5: **`u3_mirror_clamp` = S2' (`u3_corner_stmt'` of `WGapStmt_Scratch2_20261115.lean`), PROVED, no sorry**: assembly of `u3_of_suppliers` (WGapInv3) with the concrete structure `Bst` (WGapB1),
the suppliers `side3_supplier` (WGapSide3d), `case1_supplier` (WGapCase1b), `case3_supplier` (WGapCase3d) and `hthird_of_inv` (WGapTop).
Statement identical to `u3_corner_stmt'`: hypotheses exactly `Corner2`, `H4`, `1 <= J <= f-1`, the tiles `U(0,j)`, `T_j = U'(0,j)` for `j < J`; no added hypothesis.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapCase3d

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

theorem u3_mirror_clamp {e f : ℕ} {α β γ L ax ay : ℝ} (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay)
    (hH4 : H4 f ax ay) (J : ℕ) (hJ1 : 1 ≤ J) (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) :
    ∀ j : ℕ, 1 ≤ j → j ≤ J → ∃ c : ℕ, 1 ≤ c ∧ c ≤ j ∧
      (∀ i : ℕ, i < c → UTM D (e : ℝ) (f : ℝ) 1 0 (i : ℝ) ((j - 1 - i : ℕ) : ℝ)) ∧
      (j < J → ∀ i : ℕ, i < c → DTM D (e : ℝ) (f : ℝ) 1 0 (i : ℝ) ((j - 1 - i : ℕ) : ℝ)) ∧
      (∀ i : ℕ, i < c → ∃ (τ : Fin N) (W : Plane),
        HasV D τ (mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) (mpG (e : ℝ) f 1 0 ((i : ℝ) + 1) ((j : ℝ) - i - 1)) W ∧
        cross (mpG (e : ℝ) f 1 0 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 0 0 (j : ℝ)) (W - mpG (e : ℝ) f 1 0 (i : ℝ) ((j : ℝ) - i)) < 0) :=
  u3_of_suppliers S h2 J hJ1 hJf hU hT (Bst := Bst D e f) (bst_self D e f)
    (side3_supplier S h2 hH4 hJf hU hT) (case1_supplier S h2 hJf hU hT) (case3_supplier S hJf hU hT)
    (fun j c I hjJ => hthird_of_inv S hJf hU hT (by have := I.c1; have := I.cj; omega) hjJ I)

#print axioms u3_mirror_clamp

end Erdos634.Draft.WGapStmt
