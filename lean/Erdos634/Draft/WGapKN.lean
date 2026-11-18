/-
Draft/WGapKN.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P2.2, P2.3).
Not imported by any aggregate.  The imports K and N at an arbitrary lattice origin `p(c₀,0)`: `hch_origin` (the hypothesis `hch` of `CtxJ.of_K1J`), `K_at_origin`, `N_at_origin`.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapDefs3
import Erdos634.Draft.SideRunGSources
import Erdos634.Draft.SideRunGCornerA

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


section kn

variable {e f : ℕ} {α β γ L ax ay : ℝ}

/-- **the hypothesis `hch` of `CtxJ.of_K1J` at the lattice origin `p(c₀,0)`** (PROOF 2.2 "Statement-match"): at the corner (`c₀ = 0`, `Corner2`) from `hch_cornerA_two`,
at a station (`c₀ ≥ 1`) from `hch_pos`: `p(c₀,0)` is in the relative interior of the side `s` (`0 < x < L`, the right vertex `p(c₀+1,0)` of `U(c₀,0)` is in Δ) -/
theorem hch_origin (S : SetupG D e f α β γ L ax ay) (c₀ : ℕ) (hc0 : c₀ = 0 → Corner2 e f ax ay)
    (hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0) :
    ∀ j : ℕ, 1 ≤ j → lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 j ∈ D.target.carrier →
      openSegment ℝ (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0) (lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 j) ⊆
        interior D.target.carrier := by
  obtain ⟨t0, ht0⟩ := hU0
  have hP : mkPt (xo f c₀) 0 ∈ D.target.carrier := by
    have := ht0.mem₁; rwa [lpG_zero] at this
  by_cases hc : c₀ = 0
  · subst hc
    obtain ⟨t, ht, hax, hay⟩ := hc0 rfl
    have hx : xo f 0 = 0 := by simp [xo]
    rw [hx] at hP ⊢
    exact hch_cornerA_two S ht hax hay hP
  · have hc' : (0 : ℝ) < c₀ := by exact_mod_cast Nat.pos_of_ne_zero hc
    have hf2 := S.c_pos
    have hx0 : 0 < xo f c₀ := by unfold xo; positivity
    have hp1 : lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) (0 + 1) 0 ∈ D.target.carrier := ht0.mem₂
    have e1 : lpG (e : ℝ) (f : ℝ) 1 (xo f c₀) 1 0 = mkPt (xo f c₀ + (f : ℝ) ^ 2) 0 := by
      unfold lpG; exact mkPt_congr (by ring) (by ring)
    rw [zero_add, e1] at hp1
    have hB := (S.mem hp1).2.2
    rw [gB_mk] at hB
    have hay := S.hay
    have hxL : xo f c₀ < L := by nlinarith
    exact S.hch_pos hx0 hxL hP

/-- **Theorem K at the origin `p(c₀,0)`** with (K1) at the row `js` (= `CtxJ.K_allGJ` through `CtxJ.of_K1J` and `hch_origin`) -/
theorem K_at_origin (S : SetupG D e f α β γ L ax ay) (c₀ js : ℕ) (hc0 : c₀ = 0 → Corner2 e f ax ay)
    (hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0) (hK1 : K1J D (e : ℝ) (f : ℝ) 1 (xo f c₀) js) :
    ∀ m : ℕ, 1 ≤ m → AGJ D e f 1 (xo f c₀) js m :=
  (CtxJ.of_K1J S (Or.inl rfl) (hch_origin S c₀ hc0 hU0) hK1).K_allGJ

/-- **Lemma N at the origin `p(c₀,0)`** (= `CtxJ.noNJ`) -/
theorem N_at_origin (S : SetupG D e f α β γ L ax ay) (c₀ js : ℕ) (hc0 : c₀ = 0 → Corner2 e f ax ay)
    (hU0 : UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) 0 0) (hK1 : K1J D (e : ℝ) (f : ℝ) 1 (xo f c₀) js) :
    ∀ i j : ℕ, js ≤ j → i + j + 2 ≤ f →
    (∀ i' j' : ℕ, j' ≤ j → i' + j' ≤ i + j → UTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) i' j') →
    (∀ i' j' : ℕ, j' < j → i' + j' + 1 ≤ i + j → DTG D (e : ℝ) (f : ℝ) 1 (xo f c₀) i' j') →
    (∀ m' : ℕ, 1 ≤ m' → m' ≤ i → AGJ D e f 1 (xo f c₀) js m') → ¬ NTile D e f c₀ i j := by
  intro i j hjs hij hU hD hA ⟨t, ht⟩
  exact (CtxJ.of_K1J S (Or.inl rfl) (hch_origin S c₀ hc0 hU0) hK1).noNJ i j hjs hij hU hD hA t ht

end kn

#print axioms hch_origin
#print axioms K_at_origin
#print axioms N_at_origin

end Erdos634.Draft.WGapStmt
