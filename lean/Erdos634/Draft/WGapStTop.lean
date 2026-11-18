/-
Draft/WGapStTop.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapTop` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapTop
import Erdos634.Draft.WGapStInv2

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set

open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv

variable {N : ℕ} {D : CongruentDissection N}

/-- the point `X0 - eps s_j` as a point of the cone of `U(0,j-1)` at `p(0,j)` -/
theorem top_pt {e f x : ℝ} (he : 0 < e) (hef : e < f) (j ε : ℝ) :
    mpG e f 1 x 0 j + ε • ((mpG e f 1 x 0 j + (-1 : ℝ) • (mpG e f 1 x 1 (j - 1) - mpG e f 1 x 0 j)) - mpG e f 1 x 0 j) =
      lpG e f 1 x 0 (j - 1 + 1) + ε • ((sMir e f - 2) • (lpG e f 1 x 0 (j - 1) - lpG e f 1 x 0 (j - 1 + 1)) +
        (1 : ℝ) • (lpG e f 1 x (0 + 1) (j - 1) - lpG e f 1 x 0 (j - 1 + 1))) := by
  rw [mpG_eq_zero he hef x j, mpG_eq he hef]
  unfold lpG
  ext i
  fin_cases i <;> simp <;> ring

section top

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

theorem top_clamp (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    {j n : ℕ} (hj1 : J0 + 1 ≤ j) (hjJ : j ≤ J) (hn : 1 ≤ n) :
    ∀ ed ∈ D.lineChain (crossL (sj e f x j)) (cross (sj e f x j) (mpG (e : ℝ) f 1 x 0 (j : ℝ))),
      ¬ Straddles ((D.tile ed.1).edge ed.2)
        (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (-1 : ℝ) • sj e f x j) (mpG (e : ℝ) f 1 x 0 (j : ℝ))
        (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (n : ℝ) • sj e f x j) := by
  intro ed _
  have hcast : (((j - 1 : ℕ)) : ℝ) = (j : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  obtain ⟨t, ht⟩ := hU (j - 1) (by omega) (by omega)
  rw [hcast] at ht
  have hs2 := sMir_gt_two S.e0 S.hef'
  obtain ⟨ε₀, hε₀, hpush⟩ := hasV_push ht.rot.rot (θ1 := sMir (e : ℝ) f - 2) (θ2 := 1) (by linarith) one_pos
  refine not_straddles_short D.toDissection (j := t) hε₀ (ρ := (n : ℝ)) (by exact_mod_cast hn) ?_ ?_ ed.1 ed.2
  · unfold sj; ext i; simp; ring
  · intro ε h0 h1
    have h := hpush ε h0 h1
    unfold sj
    rw [top_pt S.e0 S.hef' (j : ℝ) ε]
    exact h

set_option maxHeartbeats 1000000 in
/-- **(U3-c) at level `j <= J`** from the invariant: a far-side tile over every a-step of the chord -/
theorem hthird_of_inv (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1))
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) {Bst : ℕ → ℕ → Prop} {j c : ℕ} (hj1 : J0 + 1 ≤ j) (hjJ : j ≤ J)
    (I : Inv D e f x J0 Bst j c) :
    ∀ i : ℕ, i < c → ∃ (τ : Fin N) (W : Plane),
        HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - i)) (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) ((j : ℝ) - i - 1)) W ∧
        cross (mpG (e : ℝ) f 1 x 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 x 0 (j : ℝ)) (W - mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - i)) < 0 := by
  have hn : c ≤ f - 1 := by have := I.cj; omega
  have hnorm : ‖sj e f x j‖ = (e : ℝ) * f := by
    unfold sj; exact mirror_step_norm S.e0 S.hef' x (j : ℝ)
  have hef : (0 : ℝ) < (e : ℝ) * f := S.a_pos
  have hs0 : sj e f x j ≠ 0 := by
    intro h; rw [h, norm_zero] at hnorm; linarith
  obtain ⟨hint, hwall⟩ := inv_hint_wall S hU hT hj1 hjJ I
  have hint' : openSegment ℝ (mpG (e : ℝ) f 1 x 0 (j : ℝ)) (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (c : ℝ) • sj e f x j) ⊆ interior D.target.carrier := hint
  have hwall' : ∀ y ∈ openSegment ℝ (mpG (e : ℝ) f 1 x 0 (j : ℝ)) (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (c : ℝ) • sj e f x j),
      ∀ i, y ∉ interior (D.tile i).carrier := hwall
  have key := chord_all S (crossL (sj e f x j)) (Erdos634.Geometry.crossL_ne_zero hs0) (cross (sj e f x j) (mpG (e : ℝ) f 1 x 0 (j : ℝ))) hs0 hnorm
    (crossL_apply _ _) (by rw [crossL_apply]; simp [cross]; ring) I.c1 hn hint' hwall'
    (top_clamp S hU hj1 hjJ I.c1) I.clamp
  intro i hi
  obtain ⟨τ, W, hV, hW⟩ := key i hi
  have h1 : mpG (e : ℝ) f 1 x 0 (j : ℝ) + (i : ℝ) • sj e f x j = mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - i) := by
    unfold sj; exact step_pt S.e0 S.hef' x (j : ℝ) (i : ℝ)
  have h2 : mpG (e : ℝ) f 1 x 0 (j : ℝ) + ((i : ℝ) + 1) • sj e f x j =
      mpG (e : ℝ) f 1 x ((i : ℝ) + 1) ((j : ℝ) - i - 1) := by
    unfold sj
    exact (step_pt S.e0 S.hef' x (j : ℝ) ((i : ℝ) + 1)).trans (mpG_congr' rfl (by ring))
  refine ⟨τ, W, ?_, ?_⟩
  · rw [h1, h2] at hV; exact hV
  · show cross (sj e f x j) (W - mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - i)) < 0
    have e1 : cross (sj e f x j) (W - (mpG (e : ℝ) f 1 x 0 (j : ℝ) + (i : ℝ) • sj e f x j)) =
        crossL (sj e f x j) W - cross (sj e f x j) (mpG (e : ℝ) f 1 x 0 (j : ℝ)) := by
      rw [crossL_apply]; simp [cross]; ring
    rw [← h1, e1]; linarith


end top

end Erdos634.Draft.WGapSt
