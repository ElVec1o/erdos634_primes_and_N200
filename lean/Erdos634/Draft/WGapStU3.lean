/-
Draft/WGapStU3.lean -- written 15 November 2026 (session 7).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P6.3).
Not imported by any aggregate.  STATION port of `WGapInv3` (lattice origin `x`, absolute levels, floor `J0`); see WGapStInv1.  No sorry, no native_decide.
-/
import Erdos634.Draft.WGapStSide3
import Erdos634.Draft.WGapStCase3
import Erdos634.Draft.WGapStTop

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.WGapSt

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose
  Erdos634.RunPartition Erdos634.E1BaseWord Erdos634.WallEndpoints Erdos634.BaseChain
  Erdos634.Placement Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.TilePlacement
  Erdos634.Geometry.Dissection Erdos634.Draft.W2E1 Erdos634.Draft.SideRun Erdos634.Draft.SideRunG
  Erdos634.Draft.SideRunGJ Erdos634.Draft.SideRunGA Set Erdos634.Draft.WGapStmt

variable {N : ℕ} {D : CongruentDissection N}


open Erdos634.Draft.WGapStmt hiding sj BotClamp Inv Unfl Flip utm_cast nearOK_inv level_known inv_hint_wall level_data ha_succ hDp_succ unfl_utm inv_step top_pt top_clamp hthird_of_inv ub ClampB FlipAt Bst bst_self ub_norm ub_ne clampB_outside clampB_tile

section stu3

variable {e f : ℕ} {α β γ L ax ay : ℝ} {x : ℝ} {J0 : ℕ}

/-- **the `side3` supplier at a station**: at `c + J0 = j` the alpha-wedge at the wall point `q'(c,J0)` is `U'` or the flipped tile -/
theorem side3_supplier_st (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1))
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) (hW : WallOK D e f x J0)
    {Bst : ℕ → ℕ → Prop} {j c : ℕ} (hj1 : J0 + 1 ≤ j) (hjJ : j < J) (I : Inv D e f x J0 Bst j c) (hc : c + J0 = j) :
    Unfl D e f x j c ∨ Flip D e f x j c := by
  have hc1 := I.c1
  have hjc : (j : ℝ) - (c : ℝ) = (J0 : ℝ) := by
    have : ((c + J0 : ℕ) : ℝ) = (j : ℝ) := by rw [hc]
    push_cast at this; linarith
  have hcR : ((c - 1 : ℕ) : ℝ) = (c : ℝ) - 1 := by rw [Nat.cast_sub hc1]; simp
  -- U'(c-1, J0)
  obtain ⟨tU, hUt⟩ := I.ha (c - 1) J0 (by omega) le_rfl (by omega)
  rw [hcR] at hUt
  have hU1 : ∃ t, HasV D t (mpG (e : ℝ) f 1 x (c : ℝ) (J0 : ℝ)) (mpG (e : ℝ) f 1 x ((c : ℝ) - 1) ((J0 : ℝ) + 1))
      (mpG (e : ℝ) f 1 x ((c : ℝ) - 1) (J0 : ℝ)) := by
    refine ⟨tU, ?_⟩
    have := hUt.rot
    refine hasV_congr this ?_ ?_ ?_
    · exact mpG_congr' (by ring) rfl
    · exact mpG_congr' rfl rfl
    · exact mpG_congr' rfl rfl
  -- D'(c-1, J0)
  obtain ⟨hD, -⟩ := level_data S hJf hU hT hj1 hjJ I
  obtain ⟨tD, hDt⟩ := hD (c - 1) (by omega)
  have e1 : j - 1 - (c - 1) = J0 := by omega
  rw [e1, hcR] at hDt
  have hD' : ∃ t, HasV D t (mpG (e : ℝ) f 1 x (c : ℝ) (J0 : ℝ)) (mpG (e : ℝ) f 1 x (c : ℝ) ((J0 : ℝ) + 1))
      (mpG (e : ℝ) f 1 x ((c : ℝ) - 1) ((J0 : ℝ) + 1)) := by
    refine ⟨tD, ?_⟩
    refine hasV_congr hDt.swap.rot ?_ ?_ ?_ <;> exact mpG_congr' (by ring) (by ring)
  have hWt := hW c hc1 (by have := I.cj; have := hJf; omega) (fun t ht => by
    obtain ⟨τ, hτ⟩ := I.ha t J0 ht le_rfl (by omega)
    exact ⟨τ, hτ⟩)
  have h := side3_fill_st S (c : ℝ) (J0 : ℝ) hU1 hD' hWt
  simp only [Unfl, Flip, hjc]
  exact h

theorem inv_one (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1)) (hW : WallOK D e f x J0) (hJ : J0 + 1 ≤ J)
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) :
    Inv D e f x J0 (Bst D e f x J0) (J0 + 1) 1 := by
  refine ⟨le_rfl, by omega, ?_, ?_, ?_, bst_self D e f x J0 _ _ (by omega)⟩
  · intro i i' hi hi' hii
    have h0 : i = 0 := by omega
    have h0' : i' = J0 := by omega
    subst h0
    rw [h0']
    simpa using hT J0 le_rfl (by omega)
  · intro i hi; omega
  · exact side1_supplier S hJf hW (j := J0) (c := 0) (by omega) (by omega) (fun t ht => by
      have : t = 0 := by omega
      subst this; simpa using hT J0 le_rfl (by omega))

theorem inv_all (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1)) (hW : WallOK D e f x J0) (hJ : J0 + 1 ≤ J)
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) :
    ∀ j : ℕ, J0 + 1 ≤ j → j ≤ J → ∃ c : ℕ, Inv D e f x J0 (Bst D e f x J0) j c := by
  intro j hj
  induction j, hj using Nat.le_induction with
  | base => intro _; exact ⟨1, inv_one S hJf hW hJ hT⟩
  | succ j hj ih =>
    intro hjJ
    obtain ⟨c, I⟩ := ih (by omega)
    exact inv_step S hJf hU hT (Bst := Bst D e f x J0) (fun j c hc => bst_self D e f x J0 j c (by omega))
      (fun j c _ hjJ' hc hall => side1_supplier S hJf hW hjJ' hc hall)
      (fun j c I' hjJ' hc => side3_supplier_st S hJf hU hT hW (by have := I'.c1; omega) hjJ' I' hc)
      (case1_supplier S hJf hU hT hW) (case3_supplier S hJf hU hT) hj (by omega) I

/-- **Lemma U3-ST in absolute levels (S3')**: the conclusion of `u3_mirror_clamp` at the station `(x, J0)`; `J` is the absolute top level `J0 + H` -/
theorem u3_st_abs (S : SetupG D e f α β γ L ax ay) {J : ℕ} (hJf : J ≤ J0 + (f - 1)) (hW : WallOK D e f x J0) (hJ : J0 + 1 ≤ J)
    (hU : ∀ j : ℕ, J0 ≤ j → j < J → UTG D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ))
    (hT : ∀ j : ℕ, J0 ≤ j → j < J → UTM D (e : ℝ) (f : ℝ) 1 x 0 (j : ℝ)) :
    ∀ j : ℕ, J0 + 1 ≤ j → j ≤ J → ∃ c : ℕ, 1 ≤ c ∧ c + J0 ≤ j ∧
      (∀ i : ℕ, i < c → UTM D (e : ℝ) f 1 x (i : ℝ) ((j - 1 - i : ℕ) : ℝ)) ∧
      (j < J → ∀ i : ℕ, i < c → DTM D (e : ℝ) f 1 x (i : ℝ) ((j - 1 - i : ℕ) : ℝ)) ∧
      (∀ i : ℕ, i < c → ∃ (τ : Fin N) (W : Plane),
        HasV D τ (mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - i)) (mpG (e : ℝ) f 1 x ((i : ℝ) + 1) ((j : ℝ) - i - 1)) W ∧
        cross (mpG (e : ℝ) f 1 x 1 ((j : ℝ) - 1) - mpG (e : ℝ) f 1 x 0 (j : ℝ)) (W - mpG (e : ℝ) f 1 x (i : ℝ) ((j : ℝ) - i)) < 0) := by
  intro j hj1 hjJ
  obtain ⟨c, I⟩ := inv_all S hJf hW hJ hU hT j hj1 hjJ
  refine ⟨c, I.c1, I.cj, ?_, ?_, hthird_of_inv S hJf hU hT hj1 hjJ I⟩
  · intro i hi
    exact I.ha i (j - 1 - i) hi (by have := I.cj; omega) (by have := I.cj; omega)
  · intro hjJ' i hi
    exact (level_data S hJf hU hT hj1 hjJ' I).1 i hi

end stu3

#print axioms u3_st_abs

end Erdos634.Draft.WGapSt
