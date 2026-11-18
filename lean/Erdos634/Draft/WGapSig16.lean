/-
Draft/WGapSig16.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.3: the chord `[O,Y]`).
Not imported by any aggregate.  No sorry, no native_decide.
`chord_O_int`, `chord_O_bdry`: the front parts of `dich_fill_int` / `dich_fill_bdry` (the angle count `no_straddle` at `O`) as lemmas: the CLAMP AT `O` of the chord `[O,Y]` (no chain edge of the line
`O + R (Y − O)` straddles `O`), the interior-ness of the open chord and `O ≠ Y`.  Verbatim copies of the proofs, with another conclusion.
-/
import Erdos634.Draft.WGapSig15

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

section sig16

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 2000000 in
theorem chord_O_int (S : SetupG D e f α β γ L ax ay) (x a η : ℝ)
    {tDL tUl tDl tUr tUi tN tE : Fin N}
    (hDL : HasV D tDL (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hUl : HasV D tUl (lpG (e : ℝ) f 1 x (a + 1) η) (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)))
    (hDl : HasV D tDl (lpG (e : ℝ) f 1 x (a + 1 + 1) η) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1 + 1) (η + 1)))
    (hUr : HasV D tUr (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1 + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x a (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x a (η + 1 + 1))
      (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f)))
    (hE : HasV D tE (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) (lpG (e : ℝ) f 1 x (a + 1) (η + 1 + 1))
      (lpG (e : ℝ) f 1 x a (η + 1 + sMir (e : ℝ) f))) :
    ∃ P' : Plane, cross (ptY e f x a (η + 1) - ptO e f x a (η + 1)) (P' - ptO e f x a (η + 1)) = 0 ∧
      ptO e f x a (η + 1) ∈ openSegment ℝ P' (ptY e f x a (η + 1)) ∧
      (∀ ed ∈ D.lineChain (crossL (ptY e f x a (η + 1) - ptO e f x a (η + 1))) (cross (ptY e f x a (η + 1) - ptO e f x a (η + 1)) (ptO e f x a (η + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (ptO e f x a (η + 1)) (ptY e f x a (η + 1))) ∧
      openSegment ℝ (ptO e f x a (η + 1)) (ptY e f x a (η + 1)) ⊆ interior D.target.carrier ∧
      ptO e f x a (η + 1) ≠ ptY e f x a (η + 1) := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA := S.hA
  have hsM := sMir_gt_two he0 hef
  have hnu0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos hb (by positivity)
  have hsm := sMir_mul he0 hef
  obtain ⟨aDL, aUl, aDl, aUr, hOint, n12, n13, n14, n23, n24, n34⟩ := lower_half S hε hDL hUl hDl hUr
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  -- the angle of `E′` at `O`
  have aE : (D.tile tE).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = α := by
    refine ((hE.anglesG S.tile S.hM).1) ?_
    refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
    have e1 : a + 1 - a = 1 := by ring
    have e2 : η + 1 + 1 - (η + 1 + sMir (e : ℝ) f) = 1 - sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
  -- distinctness inside the classes `α`: `{DL, Ur, E′}`, `β`: `{Dl, Ui, N}`
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) 1 p ≤ -lvG (e : ℝ) (f : ℝ) 1 x (a + (η + 1) + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) 1) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have hyDl : ∀ i, ((D.tile tDl).pts i) 1 ≤ (η + 1) * hhG (e : ℝ) (f : ℝ) :=
    hDl.all (P := fun p => p 1 ≤ (η + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl) (lpG_y_le he0 hef le_rfl)
  have nUiDl : tUi ≠ tDl := by
    obtain ⟨k, hk⟩ := hUi.idx₃
    exact (ne_of_F (fun p : Plane => p 1) hyDl (i := k)
      (by rw [hk]; exact lpG_y_gt he0 hef (by linarith))).symm
  have nNDl : tN ≠ tDl := by
    obtain ⟨k, hk⟩ := hN.idx₂
    exact (ne_of_F (fun p : Plane => p 1) hyDl (i := k)
      (by rw [hk]; exact lpG_y_gt he0 hef (by linarith))).symm
  have nDLE : tE ≠ tDL := by
    obtain ⟨k, hk⟩ := hasV_third hE
    refine HasV.ne_of_vertex hDL hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  have nUrE : tE ≠ tUr := by
    obtain ⟨k, hk⟩ := hasV_third hE
    refine HasV.ne_of_vertex hUr hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  set K : Finset (Fin N) := {tDL, tUl, tDl, tUr, tUi, tN, tE} with hKdef
  have hang : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = u →
      (D.tile j).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) (η + 1)) = 2 * Real.pi - α := by
    rw [hKdef, sum_seven _ n12 n13 n14 (hang _ _ aDL aUi hαβ) (hang _ _ aDL aN hαβ) nDLE.symm
      n23 n24 (hang _ _ aUl aUi hβγ.symm) (hang _ _ aUl aN hβγ.symm) (hang _ _ aUl aE hαγ.symm)
      n34 nUiDl.symm nNDl.symm (hang _ _ aDl aE hαβ.symm)
      (hang _ _ aUr aUi hαβ) (hang _ _ aUr aN hαβ) nUrE.symm
      nUiN (hang _ _ aUi aE hαβ.symm) (hang _ _ aN aE hαβ.symm), aDL, aUl, aDl, aUr, aUi, aN, aE]
    have hr := hA.hrel
    have hg := hA.hγdef
    linarith
  set O := lpG (e : ℝ) f 1 x (a + 1) (η + 1) with hOdef
  set Y := lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η + 1 + 2 + nuG (e : ℝ) f) with hYdef
  have hΩ : ∑ i, (D.tile i).localAngle O = 2 * Real.pi := by
    have := D.toDissection.sum_localAngle_eq O
    rw [this, D.target.localAngle_interior hOint]
  have hXY : O ≠ Y := by
    intro h
    have := lpG_eta_eq he0 hef h
    linarith
  have hYt : Y ∈ D.target.carrier := hN.mem₃
  have hint := openSeg_interior D.toDissection hOint hYt
  have hP' : cross (Y - O) ((O - (Y - O)) - O) = 0 := by
    simp [cross]; ring
  have hXP : O ∈ openSegment ℝ (O - (Y - O)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle O < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [aDL]; exact hαπ
    · rw [aUl]; exact hγπ
    · rw [aDl]; exact hβπ
    · rw [aUr]; exact hαπ
    · rw [aUi]; exact hβπ
    · rw [aN]; exact hβπ
    · rw [aE]; exact hαπ
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) hKsum hαπ hKlt
  exact ⟨O - (Y - O), hP', hXP, hclamp, hint, hXY⟩

set_option maxHeartbeats 2000000 in
theorem chord_O_bdry (S : SetupG D e f α β γ L ax ay) (x a η0 : ℝ)
    {tUa tUi tN tE : Fin N}
    (hUa : HasV D tUa (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x (a + 1 + 1) η0) (lpG (e : ℝ) f 1 x (a + 1) (η0 + 1)))
    (hUi : HasV D tUi (lpG (e : ℝ) f 1 x a η0) (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x a (η0 + 1)))
    (hN : HasV D tN (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x a (η0 + 1))
      (lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η0 + 2 + nuG (e : ℝ) f)))
    (hE : HasV D tE (lpG (e : ℝ) f 1 x (a + 1) η0) (lpG (e : ℝ) f 1 x (a + 1) (η0 + 1))
      (lpG (e : ℝ) f 1 x a (η0 + sMir (e : ℝ) f)))
    (hη0 : 0 ≤ η0)
    (hfr : lpG (e : ℝ) f 1 x (a + 1) η0 ∈ frontier D.target.carrier ∧
      lpG (e : ℝ) f 1 x (a + 1) η0 ∉ Set.range D.target.pts) :
    ∃ P' : Plane, cross (ptY e f x a η0 - ptO e f x a η0) (P' - ptO e f x a η0) = 0 ∧
      ptO e f x a η0 ∈ openSegment ℝ P' (ptY e f x a η0) ∧
      (∀ ed ∈ D.lineChain (crossL (ptY e f x a η0 - ptO e f x a η0)) (cross (ptY e f x a η0 - ptO e f x a η0) (ptO e f x a η0)),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (ptO e f x a η0) (ptY e f x a η0)) ∧
      openSegment ℝ (ptO e f x a η0) (ptY e f x a η0) ⊆ interior D.target.carrier ∧
      ptO e f x a η0 ≠ ptY e f x a η0 := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA := S.hA
  have hsM := sMir_gt_two he0 hef
  have hnu0 : 0 < nuG (e : ℝ) f := by
    unfold nuG; exact div_pos hb (by positivity)
  have hsm := sMir_mul he0 hef
  have aUa := (U_anglesG S hε hUa).1
  have aUi := (U_anglesG S hε hUi).2.1
  have aN := (N_anglesG S hε hN).1
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  obtain ⟨hαπ, hβπ, hγπ, -, -, -⟩ := angles_lt_pi S
  have aE : (D.tile tE).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = α := by
    refine ((hE.anglesG S.tile S.hM).1) ?_
    refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
    have e1 : a + 1 - a = 1 := by ring
    have e2 : η0 + 1 - (η0 + sMir (e : ℝ) f) = 1 - sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
  have hleN := hN.all (P := fun p => GSG (e : ℝ) (f : ℝ) 1 p ≤ -lvG (e : ℝ) (f : ℝ) 1 x (a + η0 + 1))
    (GSG_le he0 hef hε (by linarith)) (GSG_le he0 hef hε (by linarith))
    (GSG_le he0 hef hε (by linarith))
  have nUiN : tUi ≠ tN := by
    obtain ⟨k, hk⟩ := hUi.idx₁
    exact (ne_of_F (GSG (e : ℝ) (f : ℝ) 1) hleN (i := k)
      (by rw [hk]; exact GSG_gt he0 hef hε (by linarith))).symm
  have nUaE : tE ≠ tUa := by
    obtain ⟨k, hk⟩ := hasV_third hE
    refine HasV.ne_of_vertex hUa hk ?_ ?_ ?_ <;>
    · intro h
      have := lpG_eta_eq he0 hef h
      linarith
  set K : Finset (Fin N) := {tUa, tE, tN, tUi} with hKdef
  have hang : ∀ {i j : Fin N} (u v : ℝ), (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = u →
      (D.tile j).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = v → u ≠ v → i ≠ j :=
    fun u v hu hv huv => ne_of_angle (by rw [hu, hv]; exact huv)
  have hKsum : ∑ i ∈ K, (D.tile i).localAngle (lpG (e : ℝ) f 1 x (a + 1) η0) = Real.pi - α := by
    rw [hKdef, sum_four' _ nUaE.symm (hang _ _ aUa aN hαβ) (hang _ _ aUa aUi hαβ)
      (hang _ _ aE aN hαβ) (hang _ _ aE aUi hαβ) nUiN.symm, aUa, aE, aN, aUi]
    have hr := hA.hrel
    linarith
  set O := lpG (e : ℝ) f 1 x (a + 1) η0 with hOdef
  set Y := lpG (e : ℝ) f 1 x (a - nuG (e : ℝ) f) (η0 + 2 + nuG (e : ℝ) f) with hYdef
  have hΩ : ∑ i, (D.tile i).localAngle O = Real.pi := (D.toDissection.hasAngleSums).2.1 O hfr.1 hfr.2
  have hXY : O ≠ Y := by
    intro h
    have := lpG_eta_eq he0 hef h
    linarith
  have hYt : Y ∈ D.target.carrier := hN.mem₃
  have hint : openSegment ℝ O Y ⊆ interior D.target.carrier := by
    have C : CtxBase D e f α β γ L ax ay 1 x := ⟨S, Or.inl rfl⟩
    refine C.seg_intG (ξ := a + 1) (η := η0) (ξ' := a - nuG (e : ℝ) f) (η' := η0 + 2 + nuG (e : ℝ) f) hUa.mem₁ hYt ?_ ?_ ?_
    · exact Or.inr (by linarith)
    · exact Or.inl ⟨1, one_pos, hUa.mem₂⟩
    · refine Or.inl ⟨1, one_pos, ?_⟩
      have := hUi.mem₁
      rwa [show a + 1 - 1 = a by ring]
  have hP' : cross (Y - O) ((O - (Y - O)) - O) = 0 := by
    simp [cross]; ring
  have hXP : O ∈ openSegment ℝ (O - (Y - O)) Y := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  have hKlt : ∀ k ∈ K, (D.tile k).localAngle O < Real.pi := by
    intro k hk
    rw [hKdef] at hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · rw [aUa]; exact hαπ
    · rw [aE]; exact hαπ
    · rw [aN]; exact hβπ
    · rw [aUi]; exact hβπ
  have hclamp := no_straddle D.toDissection hXY hP' hXP hΩ K (θ := α) hKsum hαπ hKlt
  exact ⟨O - (Y - O), hP', hXP, hclamp, hint, hXY⟩

end sig16

#print axioms chord_O_int
#print axioms chord_O_bdry

end Erdos634.Draft.WGapStmt
