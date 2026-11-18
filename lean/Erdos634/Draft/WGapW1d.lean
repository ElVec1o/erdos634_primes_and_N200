/-
Draft/WGapW1d.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (Lemma 3.3 + P5 chord facts (C)).
Not imported by any aggregate.  Module W6e: `w1_chord` = W1 and the CHORD at the mirror line `m'_η` in one statement: from the four known tiles at `X = p'(0,η)` and the
interior / wall / END-clamp hypotheses of the run `[X, X + n (Y - X)]`, `Y = p'(1,η-1)`, `1 ≤ n ≤ f-1`: `D'(0,η-1)` is a tile AND every a-step of the run has a far-side tile.
The only hypotheses are those of the invariant I_j (end clamp `hEc` is the bottom clamp of I_j; hint/hwall are from the near tiles).  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapW1c

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

section w1d

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- the mirror step `Y - X = p'(1,η-1) - p'(0,η)` has length `a = e f` -/
theorem mirror_step_norm {e f : ℝ} (he0 : 0 < e) (hef : e < f) (x η : ℝ) :
    ‖mpG e f 1 x 1 (η - 1) - mpG e f 1 x 0 η‖ = e * f := by
  rw [← dist_eq_norm]
  have := dist_mp_a (x := x) (ε := 1) he0 hef (by norm_num) 0 (η - 1)
  simpa using this

set_option maxHeartbeats 1000000 in
/-- **W1 + chord at the mirror line** (see the module header). -/
theorem w1_chord (S : SetupG D e f α β γ L ax ay) (x η : ℝ)
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
    (hEc : ∀ ed ∈ D.lineChain (crossL (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (cross (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 0 η)),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 x 0 η + ((n : ℝ) + 1) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η + (n : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η)) :
    (∃ τ, HasV D τ (mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 1 (η - 1)) (mpG (e : ℝ) f 1 x 1 η)) ∧
    ∀ i : ℕ, i < n → ∃ (τ : Fin N) (W : Plane),
      HasV D τ (mpG (e : ℝ) f 1 x 0 η + (i : ℝ) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η))
        (mpG (e : ℝ) f 1 x 0 η + ((i : ℝ) + 1) • (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η)) W ∧
      crossL (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) W <
        cross (mpG (e : ℝ) f 1 x 1 (η - 1) - mpG (e : ℝ) f 1 x 0 η) (mpG (e : ℝ) f 1 x 0 η) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hXc := w1_clamp S x η hU0 hT hT1 hU1 hn1
  refine ⟨w1_no_c S x η hU0 hT hT1 hU1 hn1 hnf hint hwall hXc hEc, ?_⟩
  set X := mpG (e : ℝ) f 1 x 0 η with hXdef
  set Y := mpG (e : ℝ) f 1 x 1 (η - 1) with hYdef
  have hnorm : ‖Y - X‖ = (e : ℝ) * f := mirror_step_norm he0 hef x η
  have hXY : Y - X ≠ 0 := by
    intro h
    rw [h, norm_zero] at hnorm
    have : (0 : ℝ) < (e : ℝ) * f := mul_pos he0 hf0
    linarith
  have hFX : crossL (Y - X) X = cross (Y - X) X := crossL_apply _ _
  have hFs : crossL (Y - X) (Y - X) = 0 := by rw [crossL_apply]; simp [cross]; ring
  exact chord_all S (crossL (Y - X)) (crossL_ne_zero hXY) (cross (Y - X) X) hXY hnorm hFX hFs hn1 hnf
    hint hwall hXc hEc

end w1d

#print axioms w1_chord

end Erdos634.Draft.WGapStmt
