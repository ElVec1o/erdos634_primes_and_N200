/-
Draft/WGapDall.lean -- written 15 November 2026 (session 4).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 (D): `S'_i = D'(i, j-1-i)` for all `i < n`).
Not imported by any aggregate.  Module W7b: `chord_D_all` = `w1_chord` + the induction of `chord_D_step`.
Level `η` (the proof's `j`), chord `p'(i, η-i)`, `i ≤ n`, `1 ≤ n ≤ f-1`.  Hypotheses: the four W1 tiles at `p'(0,η)`, interior/wall/end clamp of the run (as `w1_chord`),
and `NearOK` at every inner point `p'(i, η-i)`, `1 ≤ i < n`: the near tiles `U'(i-1,η-i)`, `U'(i,η-i-1)`, `D'(i-1,η-i-1)` (invariant (a) and the level `j-1` far tile, F5).
Conclusion: `D'(i, η-1-i)` is a tile for all `i < n`.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapDstep

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

theorem hasV_congr {t : Fin N} {A B C A' B' C' : Plane} (h : HasV D t A B C) (h1 : A = A') (h2 : B = B') (h3 : C = C') :
    HasV D t A' B' C' := by subst h1; subst h2; subst h3; exact h

/-- the points of the chord: `p'(0,η) + t (p'(1,η-1) - p'(0,η)) = p'(t, η - t)` -/
theorem step_pt {e f : ℝ} (he : 0 < e) (hef : e < f) (x η t : ℝ) :
    mpG e f 1 x 0 η + t • (mpG e f 1 x 1 (η - 1) - mpG e f 1 x 0 η) = mpG e f 1 x t (η - t) := by
  have h := lineMap_mpG he hef x 0 η 1 (η - 1) t
  rw [AffineMap.lineMap_apply] at h
  simp only [vsub_eq_sub, vadd_eq_add] at h
  rw [add_comm, h]
  exact mpG_congr' (by ring) (by ring)

/-- the three known near tiles at `p'(ξ,η)` (hypotheses `hU1 hU2 hD1` of `chord_D_step`) -/
def NearOK (D : CongruentDissection N) (e f : ℝ) (x ξ η : ℝ) : Prop :=
  (∃ t, HasV D t (mpG e f 1 x ξ η) (mpG e f 1 x (ξ - 1) (η + 1)) (mpG e f 1 x (ξ - 1) η)) ∧
  (∃ t, HasV D t (mpG e f 1 x ξ η) (mpG e f 1 x ξ (η - 1)) (mpG e f 1 x (ξ + 1) (η - 1))) ∧
  (∃ t, HasV D t (mpG e f 1 x ξ η) (mpG e f 1 x ξ (η - 1)) (mpG e f 1 x (ξ - 1) η))

section dall

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 1000000 in
theorem chord_D_all (S : SetupG D e f α β γ L ax ay) (x η : ℝ)
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
        (mpG (e : ℝ) f 1 x 0 η))
    (hnear : ∀ i : ℕ, 1 ≤ i → i < n → NearOK D (e : ℝ) f x (i : ℝ) (η - (i : ℝ))) :
    ∀ i : ℕ, i < n → ∃ τ, HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) (η - (i : ℝ)))
      (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η - (i : ℝ) - 1)) (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) (η - (i : ℝ))) := by
  have he0 : (0 : ℝ) < e := by exact_mod_cast S.he
  have hef : (e : ℝ) < f := by exact_mod_cast S.hef
  obtain ⟨hD0, hfar⟩ := w1_chord S x η hU0 hT hT1 hU1 hn1 hnf hint hwall hEc
  set X0 := mpG (e : ℝ) f 1 x 0 η with hX0
  set Y0 := mpG (e : ℝ) f 1 x 1 (η - 1) with hY0
  have hsp := step_pt he0 hef x η
  intro i
  induction i with
  | zero =>
    intro _
    obtain ⟨τ, hτ⟩ := hD0
    refine ⟨τ, hasV_congr hτ ?_ ?_ ?_⟩
    · exact mpG_congr' (by simp) (by simp)
    · exact mpG_congr' (by simp) (by simp)
    · exact mpG_congr' (by simp) (by simp)
  | succ i ih =>
    intro hi
    obtain ⟨τ', hτ'⟩ := ih (by omega)
    obtain ⟨τ, W, hV, hW⟩ := hfar (i + 1) hi
    obtain ⟨hn1', hn2', hn3'⟩ := hnear (i + 1) (by omega) hi
    rw [hsp, hsp] at hV
    have hW' : cross (mpG (e : ℝ) f 1 x (((i + 1 : ℕ) : ℝ) + 1) (η - (((i + 1 : ℕ) : ℝ) + 1)) -
        mpG (e : ℝ) f 1 x ((i + 1 : ℕ) : ℝ) (η - ((i + 1 : ℕ) : ℝ))) (W - mpG (e : ℝ) f 1 x ((i + 1 : ℕ) : ℝ) (η - ((i + 1 : ℕ) : ℝ))) < 0 := by
      rw [← hsp (((i + 1 : ℕ) : ℝ) + 1), ← hsp ((i + 1 : ℕ) : ℝ)]
      have h1 : X0 + (((i + 1 : ℕ) : ℝ) + 1) • (Y0 - X0) - (X0 + ((i + 1 : ℕ) : ℝ) • (Y0 - X0)) = Y0 - X0 := by module
      rw [h1]
      have h2 : cross (Y0 - X0) (W - (X0 + ((i + 1 : ℕ) : ℝ) • (Y0 - X0))) =
          cross (Y0 - X0) W - cross (Y0 - X0) X0 := by
        simp [cross]; ring
      rw [h2]
      have := hW
      rw [crossL_apply] at this
      linarith
    have hD2 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x ((i + 1 : ℕ) : ℝ) (η - ((i + 1 : ℕ) : ℝ)))
        (mpG (e : ℝ) f 1 x (((i + 1 : ℕ) : ℝ) - 1) ((η - ((i + 1 : ℕ) : ℝ)) + 1))
        (mpG (e : ℝ) f 1 x ((i + 1 : ℕ) : ℝ) ((η - ((i + 1 : ℕ) : ℝ)) + 1)) := by
      refine ⟨τ', hasV_congr hτ'.swap ?_ ?_ ?_⟩
      · exact mpG_congr' (by push_cast; ring) (by push_cast; ring)
      · exact mpG_congr' (by push_cast; ring) (by push_cast; ring)
      · exact mpG_congr' (by push_cast; ring) (by push_cast; ring)
    have hV' : HasV D τ (mpG (e : ℝ) f 1 x ((i + 1 : ℕ) : ℝ) (η - ((i + 1 : ℕ) : ℝ)))
        (mpG (e : ℝ) f 1 x (((i + 1 : ℕ) : ℝ) + 1) ((η - ((i + 1 : ℕ) : ℝ)) - 1)) W := by
      refine hasV_congr hV rfl ?_ rfl
      exact mpG_congr' rfl (by ring)
    have hW'' : cross (mpG (e : ℝ) f 1 x (((i + 1 : ℕ) : ℝ) + 1) ((η - ((i + 1 : ℕ) : ℝ)) - 1) -
        mpG (e : ℝ) f 1 x ((i + 1 : ℕ) : ℝ) (η - ((i + 1 : ℕ) : ℝ))) (W - mpG (e : ℝ) f 1 x ((i + 1 : ℕ) : ℝ) (η - ((i + 1 : ℕ) : ℝ))) < 0 := by
      have : mpG (e : ℝ) f 1 x (((i + 1 : ℕ) : ℝ) + 1) ((η - ((i + 1 : ℕ) : ℝ)) - 1) =
          mpG (e : ℝ) f 1 x (((i + 1 : ℕ) : ℝ) + 1) (η - (((i + 1 : ℕ) : ℝ) + 1)) := mpG_congr' rfl (by ring)
      rw [this]; exact hW'
    have hres := chord_D_step S x ((i + 1 : ℕ) : ℝ) (η - ((i + 1 : ℕ) : ℝ)) hn1' hn2' hn3' hD2 hV' hW''
    refine ⟨τ, hasV_congr hres.rot.rot.swap rfl ?_ ?_⟩
    · exact mpG_congr' (by push_cast; ring) (by push_cast; ring)
    · exact mpG_congr' (by push_cast; ring) (by push_cast; ring)

end dall

#print axioms chord_D_all

end Erdos634.Draft.WGapStmt
