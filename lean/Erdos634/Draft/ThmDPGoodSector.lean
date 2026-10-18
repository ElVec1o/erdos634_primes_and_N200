import Mathlib.Tactic
import Erdos634.Draft.ThmDStep33
import Erdos634.Draft.ThmDPGood
import Erdos634.Draft.ThmDWallFan

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): the `α`-tile at a good end `P`  

`sector_dichotomy_P_good` : `sector_dichotomy_P` with the frontier hypotheses at `P = lp 0 η` replaced by `PGood`
(angle sum `π` over the finite set `U`, clamp of the row west of `P`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem sector_dichotomy_P_good (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ} (hη : 0 < η)
    (hPG : PGood D (u : ℝ) (v : ℝ) ε x α η)
    {tD tN : Fin N}
    (hD : HasV D tD (lpT (u : ℝ) (v : ℝ) ε x 0 (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x 1 (η - 1))
      (lpT (u : ℝ) (v : ℝ) ε x 0 η))
    (hN : HasV D tN (lpT (u : ℝ) (v : ℝ) ε x 1 (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x 0 η)
      (lpT (u : ℝ) (v : ℝ) ε x 1 η)) :
    UTT D (u : ℝ) (v : ℝ) ε x 0 η ∨ BEastT D (u : ℝ) (v : ℝ) ε x α 0 η := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hab := S.tile.hab
  have hac := S.tile.ac
  have hbc := S.tile.bc
  have hF : GHT (u : ℝ) (v : ℝ) ≠ 0 := GHT_ne hu huv
  set c0 : ℝ := -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η) with hc0
  have hnh := nhT_pos hu huv hv2
  obtain ⟨s0, hs0, hcl⟩ := hPG.rowclamp
  have hfP : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x 0 η) = c0 := GHT_lp _ _ _ _
  have hfQ : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x 1 η) = c0 := GHT_lp _ _ _ _
  have hfP' : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x (-s0) η) = c0 := GHT_lp _ _ _ _
  have hPQ : lpT (u : ℝ) (v : ℝ) ε x 0 η ≠ lpT (u : ℝ) (v : ℝ) ε x 1 η :=
    lpT_ne_xi hu huv hv2 hε (by norm_num)
  have hP' : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (-s0) η)
      (lpT (u : ℝ) (v : ℝ) ε x 1 η) := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨s0 / (1 + s0), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one (by positivity)]; linarith
    · rw [lineMap_lpT]
      refine lpT_congr ?_ (by ring)
      field_simp; ring
  have hPmem : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ D.target.carrier := hN.mem₂
  have hQmem : lpT (u : ℝ) (v : ℝ) ε x 1 η ∈ D.target.carrier := hN.mem₃
  have hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 η) (lpT (u : ℝ) (v : ℝ) ε x 1 η) ⊆
      interior D.target.carrier := by
    have h0 := S.hhpos
    refine C.seg_intT (ξ := 0) (η := η) (ξ' := 1) (η' := η) hPmem hQmem ?_ ?_ ?_
    · exact Or.inl hη
    · exact Or.inl ⟨1, one_pos, by rw [show (0 : ℝ) + 1 = 1 by norm_num]; exact hQmem⟩
    · exact Or.inr ⟨1, one_pos, by rw [show (1 : ℝ) - 1 = 0 by norm_num]; exact hPmem⟩
  have hwall : ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 η) (lpT (u : ℝ) (v : ℝ) ε x 1 η),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hN
    refine seg_wall D.toDissection (t := tN) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨e, he, k, m, t0, hkm, hk, ht0, hm, hle, hedge, hdist⟩ :=
    next_tile D.toDissection (GHT (u : ℝ) (v : ℝ)) hF c0 hPQ hfP hfQ hfP' hP' hint hwall
      (fun e _ => hcl _ e.1 e.2)
  have hm' : (D.tile e.1).pts m = lpT (u : ℝ) (v : ℝ) ε x (0 + t0) η := by
    rw [hm, lineMap_lpT]; exact lpT_congr (by ring) (by ring)
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e'] at h; exact h
  have hγpos : 0 < γ := by rw [S.hγ]; linarith [S.hα]
  have n1 : e.1 ≠ tD := by
    obtain ⟨k2, -, -, -, -, -, hk2, -, -⟩ := hD
    exact ne_of_F (D := D) (GHT (u : ℝ) (v : ℝ)) hle (i := k2)
      (by rw [hk2]; exact GHT_gt hu huv hv2 (by linarith))
  have n2 : e.1 ≠ tN := by
    obtain ⟨k2, -, -, -, -, -, hk2, -, -⟩ := hN
    exact ne_of_F (D := D) (GHT (u : ℝ) (v : ℝ)) hle (i := k2)
      (by rw [hk2]; exact GHT_gt hu huv hv2 (by linarith))
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k m hkm
  have hkj : k ≠ j₃ := Ne.symm hjk
  have hmj : m ≠ j₃ := Ne.symm hjm
  have hang := angle_at_vertexT D hab hac hbc S.hM e.1 hkm hkj hmj
  have hop := vertex_dist_casesT D S.hM e.1 hmj
  have hk0 : (D.tile e.1).pts k = lpT (u : ℝ) (v : ℝ) ε x 0 η := hk
  have hnz : (D.tile e.1).localAngle (lpT (u : ℝ) (v : ℝ) ε x 0 η) ≠ 0 := by
    rw [← hk0]
    rcases hop with h | h | h
    · rw [hang.1 h]; exact S.hα.ne'
    · rw [hang.2.1 h]; exact hβpos.ne'
    · rw [hang.2.2 h]; exact hγpos.ne'
  have hD' : HasV D tD (lpT (u : ℝ) (v : ℝ) ε x 0 (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (0 + 1) (η - 1))
      (lpT (u : ℝ) (v : ℝ) ε x 0 ((η - 1) + 1)) :=
    hasV_congr hD rfl (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring))
  have aD : (D.tile tD).localAngle (lpT (u : ℝ) (v : ℝ) ε x 0 η) = γ := by
    have := (U_anglesT hu huv hv2 hε hab hac hbc S.hM hD').2.2
    rwa [show lpT (u : ℝ) (v : ℝ) ε x 0 ((η - 1) + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 η from lpT_congr rfl (by ring)] at this
  have hN' : HasV D tN (lpT (u : ℝ) (v : ℝ) ε x (0 + 1) (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x 0 ((η - 1) + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (0 + 1) ((η - 1) + 1)) :=
    hasV_congr hN (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring)) (lpT_congr (by ring) (by ring))
  have aN : (D.tile tN).localAngle (lpT (u : ℝ) (v : ℝ) ε x 0 η) = β := by
    have := (D_anglesT hu huv hv2 hε hab hac hbc S.hM hN').2.1
    rwa [show lpT (u : ℝ) (v : ℝ) ε x 0 ((η - 1) + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 η from lpT_congr rfl (by ring)] at this
  have hβγ := beta_ne_gamma S
  have hDN : tD ≠ tN := ne_of_angle (by rw [aD, aN]; exact hβγ.symm)
  have hsum : ∑ i ∈ ({tD, tN} : Finset (Fin N)), (D.tile i).localAngle (lpT (u : ℝ) (v : ℝ) ε x 0 η)
      = Real.pi - α := by
    rw [Finset.sum_insert (by simp [hDN]), Finset.sum_singleton, aD, aN, S.hβ, S.hγ]
    ring
  have h3α : 3 * α < Real.pi := by have := S.hβ; linarith
  obtain ⟨U, hUsum, hU⟩ := hPG.usum
  have hvD : ∃ k, (D.tile tD).pts k = lpT (u : ℝ) (v : ℝ) ε x 0 η := by
    obtain ⟨k, m, j, -, -, -, -, -, hj⟩ := hD
    exact ⟨j, hj⟩
  have hvN : ∃ k, (D.tile tN).pts k = lpT (u : ℝ) (v : ℝ) ε x 0 η := by
    obtain ⟨k, m, j, -, -, -, -, hm, -⟩ := hN
    exact ⟨m, hm⟩
  have hSU : ({tD, tN} : Finset (Fin N)) ⊆ U := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi'
    · obtain ⟨k, hk⟩ := hvD; exact hU _ k hk
    · rw [Finset.mem_singleton] at hi'; subst hi'
      obtain ⟨k, hk⟩ := hvN; exact hU _ k hk
  have hα' := residue_alpha_in D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr
    (S.hM.hα') (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α (Θ := Real.pi) (by have := S.hα; linarith)
    U hUsum {tD, tN} hSU (by rw [hsum]) e.1 (hU _ k hk0) (by simp [n1, n2]) hnz
  exact row_alpha_tile C hkm hk ht0 hm' hle hα'

theorem sector_dichotomy_PD_good (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ} (hη : 0 < η)
    (hPG : PGood D (u : ℝ) (v : ℝ) ε x α η)
    (uD : UTT D (u : ℝ) (v : ℝ) ε x 0 (η - 1)) (dN : DTT D (u : ℝ) (v : ℝ) ε x 0 (η - 1)) :
    UTT D (u : ℝ) (v : ℝ) ε x 0 η ∨ BEastT D (u : ℝ) (v : ℝ) ε x α 0 η := by
  obtain ⟨tD, hD⟩ := uD
  obtain ⟨tN, hN⟩ := dN
  refine sector_dichotomy_P_good C hη hPG (tD := tD) (tN := tN) ?_ ?_
  · exact hasV_congr hD rfl (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring))
  · exact hasV_congr hN (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring)) (lpT_congr (by ring) (by ring))

#print axioms sector_dichotomy_P_good
#print axioms sector_dichotomy_PD_good
end Erdos634.Draft.ThmDRun
