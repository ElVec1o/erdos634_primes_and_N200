/-
Draft/WGapSide3d.lean -- written 15 November 2026 (session 5).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P5 [SIDE-3]).
Not imported by any aggregate.  Module P-B4: the SIDE-3 SUPPLIER of `inv_step` (hypothesis `side3`, concrete `Bst`): from `Inv j j` (so `U'(j-1,0)` by (a) and `D'(j-1,0)` by the level step)
the alpha-wedge at `p'(j,0)` is `U'(j,0)` or the flipped tile (`side3_fill`).  Needs (H4) (`H4 f ax ay`): the only place where (H4) enters the invariant.
No sorry, no native_decide.
-/
import Erdos634.Draft.WGapSide3c

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

section side3d

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem side3_supplier (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay) {J : ℕ} (hJf : J ≤ f - 1)
    (hU : ∀ j : ℕ, j < J → UTG D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ))
    (hT : ∀ j : ℕ, j < J → UTM D (e : ℝ) (f : ℝ) 1 0 0 (j : ℝ)) :
    ∀ j c : ℕ, Inv D e f (Bst D e f) j c → j < J → c = j → Unfl D e f j j ∨ Flip D e f j j := by
  intro j c I hjJ hc
  have hj1 : 1 ≤ j := by have := I.c1; omega
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub hj1]; simp
  obtain ⟨t1, ht1⟩ := I.ha (j - 1) 0 (by omega) (by omega)
  obtain ⟨t2, ht2⟩ := (level_data S hJf hU hT hj1 hjJ I).1 (j - 1) (by omega)
  have e0 : j - 1 - (j - 1) = 0 := by omega
  rw [e0] at ht2
  rw [hcast] at ht1 ht2
  have hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 0 (j : ℝ) 0) (mpG (e : ℝ) f 1 0 ((j : ℝ) - 1) 1)
      (mpG (e : ℝ) f 1 0 ((j : ℝ) - 1) 0) := by
    refine ⟨t1, ?_⟩
    have := ht1.rot
    simp only [Nat.cast_zero, zero_add] at this
    refine hasV_congr this ?_ rfl rfl
    exact mpG_congr' (by ring) rfl
  have hD : ∃ t, HasV D t (mpG (e : ℝ) f 1 0 (j : ℝ) 0) (mpG (e : ℝ) f 1 0 (j : ℝ) 1)
      (mpG (e : ℝ) f 1 0 ((j : ℝ) - 1) 1) := by
    refine ⟨t2, ?_⟩
    have := ht2.swap.rot
    simp only [Nat.cast_zero, zero_add] at this
    refine hasV_congr this ?_ ?_ ?_
    · exact mpG_congr' (by ring) rfl
    · exact mpG_congr' (by ring) rfl
    · exact mpG_congr' (by ring) rfl
  rcases side3_fill S h2 hH4 hj1 (by have := I.cj; omega) (j : ℝ) rfl hU1 hD with h | h
  · left
    obtain ⟨τ, hτ⟩ := h
    exact ⟨τ, by simpa using hτ⟩
  · right
    obtain ⟨τ, hτ⟩ := h
    exact ⟨τ, by simpa using hτ⟩

end side3d

end Erdos634.Draft.WGapStmt
