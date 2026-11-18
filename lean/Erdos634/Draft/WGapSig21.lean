/-
Draft/WGapSig21.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.3, Theorem ST (a)).
Not imported by any aggregate.  No sorry, no native_decide.
**`st_a`: in `Ω_𝔞(s,y₀,0)` the tile `F` is `F_c`**, i.e. `¬ Pi4 D e f c₀ 0 y₀` (PROOF 7.3): the tile `Z*` beside the `a`-edge of `E_{y₀}` (`zstar`) shows `β` (four `γ`-tiles `E_{y₀}`, `U(0,y₀)`,
`N`, `Z*` at the interior point `X = p(0,y₀+1)` have no vertex figure), so `W = p(−1,y₀+1+s)` (`zstar_shape`) and `Y` is interior to its `c`-edge (`zstar_Y_push`): the chord `[O,Y]` is clamped at
`Y` (`not_straddles_short`) and at `O` (`chord_data`), and a `b`-edge of `F` on it contradicts (A5) (`chord_no_b`).
-/
import Erdos634.Draft.WGapSig20

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

section sig21

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem st_a (S : SetupG D e f α β γ L ax ay) (h2 : Corner2 e f ax ay) (hH4 : H4 f ax ay)
    {c₀ J s y₀ : ℕ} (hA : IsApex D e f c₀ J) (hJ : J ≤ y₀) (hy : y₀ < s) (hsf : s ≤ f - 1) (hn2 : 2 ≤ s - y₀)
    (hΩ : OmegaCfg D e f c₀ J s y₀ 0) : ¬ Pi4 D e f c₀ 0 y₀ := by
  rintro ⟨F, R, hFv, hFc⟩
  obtain ⟨⟨hS1, hK2, hK3⟩, -, hNt, hEt⟩ := hΩ
  have hcd := chord_data S (i := 0) hy hsf (by omega) hK2 hNt hEt
  obtain ⟨P0, hP0c, hP0m, hP0cl, hint, hOY⟩ := hcd
  obtain ⟨tN, hN⟩ := hNt
  simp only [Nat.cast_zero] at hP0c hP0m hP0cl hint hOY hFv hFc hN
  set x := xo f c₀ with hxdef
  set y : ℝ := (y₀ : ℝ) with hydef
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA' := S.hA
  have hs2 := sMir_gt_two he0 hef
  have hsm := sMir_mul he0 hef
  have hhh := hhG_pos he0 hef
  have hνpos : 0 < nuG (e : ℝ) f := by unfold nuG; exact div_pos hb hf2
  have hν1 : nuG (e : ℝ) f < 1 := by
    unfold nuG
    rw [div_lt_one hf2]
    nlinarith [pow_pos he0 2]
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA'.hα hA'.hβ hA'.hαβ hA'.hγdef hA'.hrel
  -- Z*
  obtain ⟨τ, W, hZ, hZc⟩ := zstar S h2 hH4 hA hJ (by omega)
    (fun y1 h1 h2' => by
      have := hK2.1 0 y1 (by omega) (by omega)
      rwa [Nat.cast_zero] at this) hS1
  obtain ⟨tE, hE0⟩ := hS1 y₀ hJ le_rfl
  rw [zero_add] at hE0
  obtain ⟨tU, hU⟩ := hK2.1 0 y₀ le_rfl (by omega)
  rw [Nat.cast_zero] at hU
  have hXm : mpG (e : ℝ) f 1 x 0 (y + 1) = lpG (e : ℝ) f 1 x 0 (y + 1) := mpG_eq_zero he0 hef x _
  have hP'm : mpG (e : ℝ) f 1 x 1 y = lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1) := mpG_eq he0 hef x 1 _
  have hAm : mpG (e : ℝ) f 1 x 0 y = lpG (e : ℝ) f 1 x 0 y := mpG_eq_zero he0 hef x _
  set X := lpG (e : ℝ) f 1 x 0 (y + 1) with hXdef
  set P' := lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1) with hP'def
  have hE' : HasV D tE (lpG (e : ℝ) f 1 x 0 y) P' X := hasV_congr hE0 hAm hP'm hXm
  have hZ' : HasV D τ X P' W := hasV_congr hZ hXm hP'm rfl
  have hZc' : cross (P' - X) (W - X) < 0 := by rw [← hXm, ← hP'm]; exact hZc
  have dEA : dist (lpG (e : ℝ) f 1 x 0 y) P' = (f : ℝ) ^ 2 := by
    rw [hP'def]
    refine dist_lpG he0 hef hε hf2.le ?_
    have e1 : (0 : ℝ) - (-1) = 1 := by ring
    have e2 : y - (y + sMir (e : ℝ) f * 1) = -sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * sMir (e : ℝ) f) * hsm
  have dXP : dist X P' = (e : ℝ) * f := by
    rw [hXdef, hP'def]
    refine dist_lpG he0 hef hε (mul_pos he0 hf0).le ?_
    have e1 : (0 : ℝ) - (-1) = 1 := by ring
    have e2 : y + 1 - (y + sMir (e : ℝ) f * 1) = 1 - sMir (e : ℝ) f := by ring
    rw [e1, e2]
    unfold QfG
    linear_combination (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
  have aE : (D.tile tE).localAngle X = γ := ((hE'.rot.rot.anglesG S.tile S.hM).2.2) dEA
  have aU : (D.tile tU).localAngle X = γ := (U_anglesG S hε hU).2.2
  have aN : (D.tile tN).localAngle X = γ := (N_anglesG S hε hN).2
  -- heights
  have hU1 : ∀ i, ((D.tile tU).pts i) 1 ≤ (y + 1) * hhG (e : ℝ) (f : ℝ) :=
    hU.all (P := fun p => p 1 ≤ (y + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl)
  have P'high : (y + 1) * hhG (e : ℝ) (f : ℝ) < P' 1 := lpG_y_gt he0 hef (by linarith)
  obtain ⟨iP, hiP⟩ := hasV_second hZ'
  have nUZ : tU ≠ τ := ne_of_F (fun p : Plane => p 1) hU1 (i := iP) (by rw [hiP]; exact P'high)
  have nUE : tU ≠ tE := by
    obtain ⟨i2, hi2⟩ := hE'.idx₂
    exact ne_of_F (fun p : Plane => p 1) hU1 (i := i2) (by rw [hi2]; exact P'high)
  have hXint : X ∈ interior D.target.carrier :=
    interior_of_two_tiles D.toDissection hU.mem₃ nUE.symm aE aU
      (by have := Erdos634.Draft.WGapAngles.two_gamma_gt_pi hA'; linarith)
  have nEZ : tE ≠ τ := by
    obtain ⟨iW, hiW⟩ := hasV_third hZ'
    have hcr : cross (P' - X) (lpG (e : ℝ) f 1 x 0 y - X) = kapG (e : ℝ) f := by
      rw [hP'def, hXdef, cross_lpG]; ring
    have hκ := kapG_pos he0 hef
    refine (HasV.ne_of_vertex hE' hiW ?_ ?_ ?_).symm
    · intro h; rw [h, hcr] at hZc'; linarith
    · intro h; rw [h] at hZc'; simp only [cross, PiLp.sub_apply] at hZc'; nlinarith [hZc']
    · intro h; rw [h] at hZc'; simp [cross] at hZc'
  have nNU : tN ≠ tU := by
    obtain ⟨i3, hi3⟩ := hN.idx₃
    exact (ne_of_F (fun p : Plane => p 1) hU1 (i := i3)
      (by rw [hi3]; exact lpG_y_gt he0 hef (by linarith))).symm
  have nNE : tN ≠ tE := by
    obtain ⟨iO, hiO⟩ := hN.idx₁
    refine HasV.ne_of_vertex hE' hiO ?_ ?_ ?_
    · intro h; have := lpG_xi_eq he0 hef hε h; linarith
    · intro h; have := lpG_eta_eq he0 hef h; linarith
    · intro h; have := lpG_eta_eq he0 hef h; linarith
  have nNZ : τ ≠ tN := by
    refine HasV.ne_of_vertex hN hiP ?_ ?_ ?_
    · intro h; have := lpG_xi_eq he0 hef hε h; linarith
    · intro h; have := lpG_xi_eq he0 hef hε h; linarith
    · intro h; have := lpG_xi_eq he0 hef hε h; linarith
  -- the angle of `Z*` at `X`
  obtain ⟨kz, mz, nz, hkmz, hknz, hmnz, hkz, hmz, hnz⟩ := hZ'
  have hZ'' : HasV D τ X P' W := ⟨kz, mz, nz, hkmz, hknz, hmnz, hkz, hmz, hnz⟩
  have aZ : (D.tile τ).localAngle X = β ∨ (D.tile τ).localAngle X = γ := by
    have h := vertex_angle_cases S τ hkmz hknz hmnz
    rw [hkz] at h
    rcases h with h | h | h
    · exfalso
      obtain ⟨-, hsd⟩ := sides_of_alpha S τ hkmz hknz hmnz (by rw [hkz]; exact h)
      rw [hkz, hmz, dXP] at hsd
      rcases hsd with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact S.tile.ac h1
      · exact S.tile.hab h1
    · exact Or.inl h
    · exact Or.inr h
  have hβ : (D.tile τ).localAngle X = β := by
    rcases aZ with h | h
    · exact h
    · exfalso
      obtain ⟨i3, hi3⟩ := hE'.idx₃
      have fig := fig_int S hXint hi3
      unfold FigI at fig
      have hall : ∀ i ∈ ({tE, tU, tN, τ} : Finset (Fin N)), (D.tile i).localAngle X = γ := by
        intro i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hi
        rcases hi with rfl | rfl | rfl | rfl
        · exact aE
        · exact aU
        · exact aN
        · exact h
      have c1 := card_le_angle _ γ hall
      have c4 : ({tE, tU, tN, τ} : Finset (Fin N)).card = 4 := by
        have n1 : tE ∉ ({tU, tN, τ} : Finset (Fin N)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨nUE.symm, nNE.symm, nEZ⟩
        have n2 : tU ∉ ({tN, τ} : Finset (Fin N)) := by
          simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
          exact ⟨nNU.symm, nUZ⟩
        have n3 : tN ∉ ({τ} : Finset (Fin N)) := by
          simp only [Finset.mem_singleton]; exact nNZ.symm
        rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n3,
          Finset.card_singleton]
      rw [c4] at c1
      omega
  have hW := zstar_shape S x y hZ'' hZc' hβ
  subst hW
  obtain ⟨δ, hδ, hpush⟩ := zstar_Y_push S x y hZ''
  -- the chord `[O, Y]`
  have hν := hνpos
  set O := ptO e f x 0 y with hOdef
  set Y := ptY e f x 0 y with hYdef
  have hF0 : crossL (Y - O) ≠ 0 := Erdos634.Geometry.crossL_ne_zero (sub_ne_zero.mpr (Ne.symm hOY))
  have hfX : crossL (Y - O) O = cross (Y - O) O := crossL_apply _ _
  have hfY : crossL (Y - O) Y = cross (Y - O) O := by
    rw [crossL_apply]
    simp only [cross, PiLp.sub_apply]; ring
  have hfP' : crossL (Y - O) P0 = cross (Y - O) O := by
    rw [crossL_apply]
    have := hP0c
    simp only [cross, PiLp.sub_apply] at this ⊢
    linarith
  have hfQ' : crossL (Y - O) (Y + (Y - O)) = cross (Y - O) O := by
    rw [crossL_apply]
    simp only [cross, PiLp.sub_apply, PiLp.add_apply]; ring
  have hQ' : Y ∈ openSegment ℝ O (Y + (Y - O)) := by
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    ext i; simp; ring
  obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hN
  have hwall : ∀ y2 ∈ openSegment ℝ O Y, ∀ i, y2 ∉ interior (D.tile i).carrier := by
    intro y2 hy2
    refine seg_wall D.toDissection (t := tN) hkj ?_
    rw [hk, hj]
    exact openSegment_subset_segment ℝ _ _ hy2
  have hQcl : ∀ ed ∈ D.lineChain (crossL (Y - O)) (cross (Y - O) O),
      ¬ Straddles ((D.tile ed.1).edge ed.2) (Y + (Y - O)) Y O := by
    intro ed _
    refine not_straddles_short D.toDissection (j := τ) hδ one_pos (by simp) ?_ ed.1 ed.2
    intro ε hε hεδ
    have := hpush ε hε hεδ
    rw [show Y + (Y - O) - Y = Y - O by abel]
    exact this
  have hR : crossL (Y - O) R < cross (Y - O) O := by
    rw [crossL_apply]
    have : cross (Y - O) (R - O) < 0 := hFc
    simp only [cross, PiLp.sub_apply] at this ⊢
    linarith
  exact chord_no_b S (crossL (Y - O)) hF0 (cross (Y - O) O) hOY hfX hfY hfP' hfQ' hP0m hQ' hint hwall hP0cl hQcl
    (dist_ptO_ptY he0 hef x 0 y) hFv hR

end sig21

#print axioms st_a

end Erdos634.Draft.WGapStmt
