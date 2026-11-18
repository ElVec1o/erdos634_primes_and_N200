/-
Draft/WGapSig20.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.3).
Not imported by any aggregate.  No sorry, no native_decide.
`chord_data`: from K2G, `N_i(y₀)` and `E′ = μ U(i+1,y₀)` the clamp at `O` of the chord `[O,Y]`, its interior-ness and `O ≠ Y` (`chord_O_int` / `chord_O_bdry`, as `st_dichotomy_core`).
-/
import Erdos634.Draft.WGapSig19

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

section sig20

variable {e f : ℕ} {α β γ L ax ay : ℝ}

theorem chord_data (S : SetupG D e f α β γ L ax ay) {c₀ s y₀ i : ℕ} (hy : y₀ < s) (hsf : s ≤ f - 1)
    (hi : i + 2 ≤ s - y₀) (hK2 : K2G D (e : ℝ) (f : ℝ) 1 (xo f c₀) s y₀) (hNt : NTile D e f c₀ i y₀)
    (hEt : UTM D (e : ℝ) (f : ℝ) 1 (xo f (c₀ + i + 1)) 0 (y₀ : ℝ)) :
    ∃ P' : Plane, cross (ptY e f (xo f c₀) i (y₀ : ℝ) - ptO e f (xo f c₀) i (y₀ : ℝ)) (P' - ptO e f (xo f c₀) i (y₀ : ℝ)) = 0 ∧
      ptO e f (xo f c₀) i (y₀ : ℝ) ∈ openSegment ℝ P' (ptY e f (xo f c₀) i (y₀ : ℝ)) ∧
      (∀ ed ∈ D.lineChain (crossL (ptY e f (xo f c₀) i (y₀ : ℝ) - ptO e f (xo f c₀) i (y₀ : ℝ)))
          (cross (ptY e f (xo f c₀) i (y₀ : ℝ) - ptO e f (xo f c₀) i (y₀ : ℝ)) (ptO e f (xo f c₀) i (y₀ : ℝ))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (ptO e f (xo f c₀) i (y₀ : ℝ)) (ptY e f (xo f c₀) i (y₀ : ℝ))) ∧
      openSegment ℝ (ptO e f (xo f c₀) i (y₀ : ℝ)) (ptY e f (xo f c₀) i (y₀ : ℝ)) ⊆ interior D.target.carrier ∧
      ptO e f (xo f c₀) i (y₀ : ℝ) ≠ ptY e f (xo f c₀) i (y₀ : ℝ) := by
  obtain ⟨tN, hN⟩ := hNt
  obtain ⟨tE, hE⟩ := hE_conv S c₀ i (y₀ : ℝ) hEt
  rcases Nat.eq_zero_or_pos y₀ with h0 | hpos
  · subst h0
    obtain ⟨tUa, hUa⟩ := hK2.1 (i + 1) 0 le_rfl (by omega)
    obtain ⟨tUi, hUi⟩ := hK2.1 i 0 le_rfl (by omega)
    rw [Nat.cast_add, Nat.cast_one] at hUa
    obtain ⟨hx0, hxL, -⟩ := open_shift_K2 S hK2 (n := i + 1) (by omega) (by omega)
    have hfr := S.base_frontier hx0 hxL
    have hpt : mkPt (shiftX (f : ℝ) 1 (xo f c₀) (i + 1)) 0 = lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) ((i : ℝ) + 1) ((0 : ℕ) : ℝ) := by
      unfold lpG shiftX; exact mkPt_congr (by push_cast; ring) (by simp)
    rw [hpt] at hfr
    exact chord_O_bdry S (xo f c₀) (i : ℝ) ((0 : ℕ) : ℝ) hUa hUi hN hE (Nat.cast_nonneg 0) hfr
  · obtain ⟨j, rfl⟩ : ∃ j, y₀ = j + 1 := ⟨y₀ - 1, by omega⟩
    obtain ⟨tDL, hDL⟩ := hK2.2 i j (by omega) (by omega)
    obtain ⟨tUl, hUl⟩ := hK2.1 (i + 1) j (by omega) (by omega)
    obtain ⟨tDl, hDl⟩ := hK2.2 (i + 1) j (by omega) (by omega)
    obtain ⟨tUr, hUr⟩ := hK2.1 (i + 1) (j + 1) le_rfl (by omega)
    obtain ⟨tUi, hUi⟩ := hK2.1 i (j + 1) le_rfl (by omega)
    simp only [Nat.cast_add, Nat.cast_one] at hUl hDl hUr hUi hN hE
    have key := chord_O_int S (xo f c₀) (i : ℝ) (j : ℝ) hDL hUl hDl hUr hUi hN hE
    have hy1 : (((j + 1 : ℕ)) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rw [hy1]
    exact key

end sig20

#print axioms chord_data

end Erdos634.Draft.WGapStmt
