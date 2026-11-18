/-
Draft/WGapW1b.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.3, use W1; FINDINGS F8).
Not imported by any aggregate.  Module W6c: `w1_no_c` = `w1_fill` with the c-edge alternative excluded by the clamped run `[X, X + n s]`, `s = Y - X = p'(1,η-1) - p'(0,η)`.
HYPOTHESES ADDED (none to a top-level statement of the proof): the run clamps hX, hE and interior/wall of the open run are exactly the hypotheses of `chord_all` (supplied by the invariant I_j, as in the proof).
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapChord5

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

section w1b

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
/-- **W1 with the `c`-edge alternative excluded**: `D'(0,η-1) = (X, Y, p'(1,η))` is a tile, where `X = p'(0,η)`, `Y = p'(1,η-1)`,
provided the run `[X, X + n (Y - X)]` (`1 ≤ n ≤ f - 1`) is interior, wall, and clamped at both ends. -/
theorem w1_no_c (S : SetupG D e f α β γ L ax ay) (x η : ℝ)
    (hU0 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 1 η) (lpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 η) (mpG (e : ℝ) f 1 x 0 (η + 1)))
    (hT1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 (η - 1)) (mpG (e : ℝ) f 1 x 0 (η - 1)))
    (hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x 0 η) (lpG (e : ℝ) f 1 x 0 (η - 1)) (lpG (e : ℝ) f 1 x 1 (η - 1)))
    {n : ℕ} (hn1 : 1 ≤ n) (hnf : n ≤ f - 1)
    (hint : openSegment ℝ (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)) ⊆
        interior D.target.carrier)
    (hwall : ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)),
        ∀ i, y ∉ interior (D.tile i).carrier)
    (hXc : ∀ ed ∈ D.lineChain (crossL (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (cross (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 0 η)),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 x 0 η + (-1 : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η)
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)))
    (hEc : ∀ ed ∈ D.lineChain (crossL (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (cross (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 0 η)),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 x 0 η + ((n : ℝ) + 1) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η)) :
    ∃ τ, HasV D τ (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 (η - 1)) (mpG (e : ℝ) f 1 x 1 η) := by
  rcases w1_fill S x η hU0 hT hT1 hU1 with h | ⟨τ, W, hV, hW, -, -, -⟩
  · exact h
  · exfalso
    have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
    have hef : (e : ℝ) < f := by exact_mod_cast S.hef
    have hf0 : (0 : ℝ) < f := he0.trans hef
    set X := mpG (e : ℝ) f 1 x 0 η with hXdef
    set Y := mpG (e : ℝ) f 1 x 1 (η - 1) with hYdef
    have hXY : Y - X ≠ 0 := by
      intro h
      have h' : Y = X := sub_eq_zero.mp h
      have h2 : dist Y X = (e : ℝ) * f := by
        rw [hYdef, hXdef]
        have := dist_mp_a (x := x) (ε := 1) he0 hef (by norm_num) 0 (η - 1)
        simpa using this
      rw [h', dist_self] at h2
      have : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
      linarith
    have hnorm : ‖Y - X‖ = (e : ℝ) * f := by
      rw [← dist_eq_norm, hYdef, hXdef]
      have := dist_mp_a (x := x) (ε := 1) he0 hef (by norm_num) 0 (η - 1)
      simpa using this
    have hP : mpG (e : ℝ) f 1 x ((f : ℝ) / e) (η - (f : ℝ) / e) = X + ((f : ℝ) / e) • (Y - X) := by
      have h1 := lineMap_mpG he0 hef x 0 η 1 (η - 1) ((f : ℝ) / e)
      have h2 : AffineMap.lineMap X Y ((f : ℝ) / e) = X + ((f : ℝ) / e) • (Y - X) := by
        rw [AffineMap.lineMap_apply]; simp [add_comm]
      rw [← h2, hXdef, hYdef, h1]
      exact mpG_congr' (by ring) (by ring)
    rw [hP] at hV
    have hdist : dist X (X + ((f : ℝ) / e) • (Y - X)) = (f : ℝ) ^ 2 := by
      rw [dist_eq_norm, show X - (X + ((f : ℝ) / e) • (Y - X)) = (-((f : ℝ) / e)) • (Y - X) by module,
        norm_smul, hnorm, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)]
      field_simp
    have hFX : crossL (Y - X) X = cross (Y - X) X := crossL_apply _ _
    have hFs : crossL (Y - X) (Y - X) = 0 := by rw [crossL_apply]; simp [cross]; ring
    have hWlt : crossL (Y - X) W < cross (Y - X) X := by
      rw [crossL_apply]
      have : cross (Y - X) W = cross (Y - X) (W - X) + cross (Y - X) X := by
        rw [← cross_add_right]; congr 1; abel
      rw [this]; linarith
    exact no_c_edge S (crossL (Y - X)) (crossL_ne_zero hXY) (cross (Y - X) X) hXY hnorm hFX hFs hn1 hnf
      hint hwall hXc hEc (div_pos hf0 he0) hV hWlt hdist

end w1b

#print axioms w1_no_c

end Erdos634.Draft.WGapStmt
