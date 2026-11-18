/-
Draft/WGapSig9.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b2)).
Not imported by any aggregate.  Part 1 of `bad0_false`.
-/
import Erdos634.Draft.WGapSig8

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

section sig9

variable {e f : ℕ} {α β γ L ax ay : ℝ}

set_option maxHeartbeats 4000000 in
theorem bad0_false (S : SetupG D e f α β γ L ax ay) (x y : ℝ) (hy : 0 ≤ y)
    {tE tU tD tZ ix : Fin N} {W : Plane}
    (hE : HasV D tE (mpG (e : ℝ) f 1 x 0 y) (mpG (e : ℝ) f 1 x 1 y) (mpG (e : ℝ) f 1 x 0 (y + 1)))
    (hU : HasV D tU (lpG (e : ℝ) f 1 x 0 y) (lpG (e : ℝ) f 1 x (0 + 1) y) (lpG (e : ℝ) f 1 x 0 (y + 1)))
    (hDt : HasV D tD (lpG (e : ℝ) f 1 x (0 + 1) y) (lpG (e : ℝ) f 1 x 0 (y + 1)) (lpG (e : ℝ) f 1 x (0 + 1) (y + 1)))
    (hZ : HasV D tZ (mpG (e : ℝ) f 1 x 0 (y + 1)) (mpG (e : ℝ) f 1 x 1 y) W)
    (hZc : cross (mpG (e : ℝ) f 1 x 1 y - mpG (e : ℝ) f 1 x 0 (y + 1)) (W - mpG (e : ℝ) f 1 x 0 (y + 1)) < 0)
    {k m j₃ : Fin 3} {t : ℝ} (hkm : k ≠ m) (hkj : k ≠ j₃) (hmj : m ≠ j₃)
    (hk : (D.tile ix).pts k = lpG (e : ℝ) f 1 x 0 (y + 1)) (ht : 0 < t)
    (hm : (D.tile ix).pts m = lpG (e : ℝ) f 1 x (0 + t) (y + 1))
    (hle : ∀ i, GHG (f : ℝ) ((D.tile ix).pts i) ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)))
    (hθ : (D.tile ix).localAngle (lpG (e : ℝ) f 1 x 0 (y + 1)) = β ∨ (D.tile ix).localAngle (lpG (e : ℝ) f 1 x 0 (y + 1)) = γ)
    (hlen : t * (f : ℝ) ^ 2 = (e : ℝ) * f ∨ t = 1) : False := by
  have he0 := S.e0
  have hef := S.hef'
  have hf0 : (0 : ℝ) < f := he0.trans hef
  have hf2 : (0 : ℝ) < (f : ℝ) ^ 2 := by positivity
  have hb : (0 : ℝ) < (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by nlinarith
  have hε : (1 : ℝ) ^ 2 = 1 := by norm_num
  have hA := S.hA
  have hs2 := sMir_gt_two he0 hef
  have hsm := sMir_mul he0 hef
  have hκ := kapG_pos he0 hef
  have hhh := hhG_pos he0 hef
  obtain ⟨hαβ, hαγ, -, -, hβγ, -, -, -, -, -⟩ :=
    distinct_of_pos_ne hA.hα hA.hβ hA.hαβ hA.hγdef hA.hrel
  -- conversions
  have hXm : mpG (e : ℝ) f 1 x 0 (y + 1) = lpG (e : ℝ) f 1 x 0 (y + 1) := mpG_eq_zero he0 hef x (y + 1)
  have hP'm : mpG (e : ℝ) f 1 x 1 y = lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1) := mpG_eq he0 hef x 1 y
  have hAm : mpG (e : ℝ) f 1 x 0 y = lpG (e : ℝ) f 1 x 0 y := mpG_eq_zero he0 hef x y
  set X := lpG (e : ℝ) f 1 x 0 (y + 1) with hXdef
  set P' := lpG (e : ℝ) f 1 x (-1) (y + sMir (e : ℝ) f * 1) with hP'def
  have hE' : HasV D tE (lpG (e : ℝ) f 1 x 0 y) P' X := hasV_congr hE hAm hP'm hXm
  have hZ' : HasV D tZ X P' W := hasV_congr hZ hXm hP'm rfl
  have hZc' : cross (P' - X) (W - X) < 0 := by rw [← hXm, ← hP'm]; exact hZc
  -- distances
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
  -- angles at `X`
  have aE : (D.tile tE).localAngle X = γ := ((hE'.rot.rot.anglesG S.tile S.hM).2.2) dEA
  have aU : (D.tile tU).localAngle X = γ := (U_anglesG S hε hU).2.2
  have aD : (D.tile tD).localAngle X = β := (D_anglesG S hε hDt).2.1
  -- heights
  have hU1 : ∀ i, ((D.tile tU).pts i) 1 ≤ (y + 1) * hhG (e : ℝ) (f : ℝ) :=
    hU.all (P := fun p => p 1 ≤ (y + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl)
  have hD1 : ∀ i, ((D.tile tD).pts i) 1 ≤ (y + 1) * hhG (e : ℝ) (f : ℝ) :=
    hDt.all (P := fun p => p 1 ≤ (y + 1) * hhG (e : ℝ) (f : ℝ))
      (lpG_y_le he0 hef (by linarith)) (lpG_y_le he0 hef le_rfl) (lpG_y_le he0 hef le_rfl)
  have P'high : (y + 1) * hhG (e : ℝ) (f : ℝ) < P' 1 := lpG_y_gt he0 hef (by linarith)
  obtain ⟨iP, hiP⟩ := hasV_second hZ'
  have nUZ : tU ≠ tZ := ne_of_F (fun p : Plane => p 1) hU1 (i := iP) (by rw [hiP]; exact P'high)
  have nDZ : tD ≠ tZ := ne_of_F (fun p : Plane => p 1) hD1 (i := iP) (by rw [hiP]; exact P'high)
  have nUE : tU ≠ tE := by
    obtain ⟨i2, hi2⟩ := hE'.idx₂
    exact ne_of_F (fun p : Plane => p 1) hU1 (i := i2) (by rw [hi2]; exact P'high)
  have nED : tE ≠ tD := ne_of_angle (by rw [aE, aD]; exact hβγ.symm)
  have nUD : tU ≠ tD := ne_of_angle (by rw [aU, aD]; exact hβγ.symm)
  have hκy : ∀ z : ℝ, z < y + 1 → -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (y + 1)) < -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * z) := by
    intro z hz
    nlinarith [mul_pos hf2 hhh]
  have nEix : ix ≠ tE := by
    obtain ⟨i0, hi0⟩ := hE'.idx₁
    exact ne_of_F (GHG (f : ℝ)) hle (i := i0) (by rw [hi0, GHG_lp]; exact hκy y (by linarith))
  have nUix : ix ≠ tU := by
    obtain ⟨i0, hi0⟩ := hU.idx₁
    exact ne_of_F (GHG (f : ℝ)) hle (i := i0) (by rw [hi0, GHG_lp]; exact hκy y (by linarith))
  have nDix : ix ≠ tD := by
    obtain ⟨i0, hi0⟩ := hDt.idx₁
    exact ne_of_F (GHG (f : ℝ)) hle (i := i0) (by rw [hi0, GHG_lp]; exact hκy y (by linarith))
  -- `Z*`
  have hZ'' := hZ'
  obtain ⟨kz, mz, nz, hkmz, hknz, hmnz, hkz, hmz, hnz⟩ := hZ''
  have aZ : (D.tile tZ).localAngle X = β ∨ (D.tile tZ).localAngle X = γ := by
    have h := vertex_angle_cases S tZ hkmz hknz hmnz
    rw [hkz] at h
    rcases h with h | h | h
    · exfalso
      obtain ⟨-, hsd⟩ := sides_of_alpha S tZ hkmz hknz hmnz (by rw [hkz]; exact h)
      rw [hkz, hmz, dXP] at hsd
      rcases hsd with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact S.tile.ac h1
      · exact S.tile.hab h1
    · exact Or.inl h
    · exact Or.inr h
  have hXint : X ∈ interior D.target.carrier :=
    interior_of_two_tiles D.toDissection hU.mem₃ nUE.symm aE aU
      (by have := Erdos634.Draft.WGapAngles.two_gamma_gt_pi hA; linarith)
  have nEZ : tE ≠ tZ := by
    obtain ⟨iW, hiW⟩ := hasV_third hZ'
    have hcr : cross (P' - X) (lpG (e : ℝ) f 1 x 0 y - X) = kapG (e : ℝ) f := by
      rw [hP'def, hXdef, cross_lpG]; ring
    refine (HasV.ne_of_vertex hE' hiW ?_ ?_ ?_).symm
    · intro h; rw [h, hcr] at hZc'; linarith
    · intro h; rw [h] at hZc'; simp only [cross, PiLp.sub_apply] at hZc'; nlinarith [hZc']
    · intro h; rw [h] at hZc'; simp [cross] at hZc'
  by_cases hzi : ix = tZ
  · -- the bad tile is `Z*` itself: its edge on the row has length `a` or `c`
    exfalso
    subst hzi
    have hcov := fin3_cover k m j₃ hkm hkj hmj mz
    have hac := S.tile.ac
    have hmzj : mz = j₃ := by
      rcases hcov with h | h | h
      · exfalso
        rw [h, hk] at hmz
        rw [← hmz, dist_self] at dXP
        exact (mul_pos he0 hf0).ne dXP
      · exfalso
        rw [h, hm] at hmz
        have := lpG_eta_eq he0 hef hmz.symm
        linarith
      · exact h
    have hj3 : (D.tile ix).pts j₃ = P' := by rw [← hmzj]; exact hmz
    have hdkm : dist ((D.tile ix).pts k) ((D.tile ix).pts m) = t * (f : ℝ) ^ 2 := by
      rw [hk, hm]
      exact dist_lpG he0 hef hε (by positivity) (by unfold QfG; ring)
    have hdkj : dist ((D.tile ix).pts j₃) ((D.tile ix).pts k) = (e : ℝ) * f := by
      rw [hj3, hk, dist_comm]; exact dXP
    rcases hlen with h | h
    · rcases sides_of_a_edgeG D S.tile S.hM ix hkm hkj hmj (by rw [hdkm]; exact h) with ⟨s1, -⟩ | ⟨s1, -⟩
      · rw [hdkj] at s1; exact S.tile.ac s1
      · rw [hdkj] at s1; exact S.tile.hab s1
    · have hd : dist ((D.tile ix).pts k) ((D.tile ix).pts m) = (f : ℝ) ^ 2 := by rw [hdkm, h]; ring
      rcases sides_of_c_edgeG D S.tile S.hM ix hkm hkj hmj hd with ⟨-, s2⟩ | ⟨s1, -⟩
      · rw [hj3, hm, h] at s2
        have hsq := dist_lpG_sq (e := (e : ℝ)) (f := (f : ℝ)) (ε := 1) (x := x) he0 hef hε (-1) (y + sMir (e : ℝ) f * 1) (0 + 1) (y + 1)
        rw [← hP'def, s2] at hsq
        unfold QfG at hsq
        have hQ : ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ^ 2 = (f : ℝ) ^ 4 + 2 * (f : ℝ) ^ 2 * (e : ℝ) ^ 2 := by
          linear_combination hsq + (sMir (e : ℝ) f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) - (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2) - 2 * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)) * hsm
        nlinarith [pow_pos he0 2, pow_pos hf0 2, mul_pos (pow_pos he0 2) (pow_pos he0 2)]
      · rw [hdkj] at s1; exact S.tile.hab s1
  · -- five distinct tiles at the interior vertex `X`, each showing `β` or `γ`
    have hc5 : ({tE, tU, tD, tZ, ix} : Finset (Fin N)).card = 5 := by
      have n1 : tE ∉ ({tU, tD, tZ, ix} : Finset (Fin N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨nUE.symm, nED, nEZ, nEix.symm⟩
      have n2 : tU ∉ ({tD, tZ, ix} : Finset (Fin N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨nUD, nUZ, nUix.symm⟩
      have n3 : tD ∉ ({tZ, ix} : Finset (Fin N)) := by
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨nDZ, nDix.symm⟩
      have n4 : tZ ∉ ({ix} : Finset (Fin N)) := by
        simp only [Finset.mem_singleton]; exact fun h => hzi h.symm
      rw [Finset.card_insert_of_notMem n1, Finset.card_insert_of_notMem n2, Finset.card_insert_of_notMem n3,
        Finset.card_insert_of_notMem n4, Finset.card_singleton]
    obtain ⟨i3, hi3⟩ := hE'.idx₃
    refine no_five_bg S hXint hi3 _ (by rw [hc5]) ?_
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr aE
    · exact Or.inr aU
    · exact Or.inl aD
    · exact aZ
    · exact hθ

end sig9

#print axioms bad0_false

end Erdos634.Draft.WGapStmt
