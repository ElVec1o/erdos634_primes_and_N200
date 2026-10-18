import Mathlib.Tactic
import Erdos634.Draft.ThmDSector3

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' (R5 sector step 4): the `α`-tile at the end `P` on the side `S'`  

`sector_dichotomy_P` : at `P = lp 0 η`, a frontier non-vertex of the target on the side line of the corner (west of `P` is outside),
with `Δ_{0,η-1}` (`γ` at `P`) and `∇_{0,η-1}` (`β` at `P`) present: `Δ_{0,η}` is a tile or a tile north of the row has `α` at `P` and a
`b`-edge running east (`BEastT`).  The boundary version of `sector_dichotomy` (`G_w` of Lemma 33): the sum of angles at `P` is `π`,
`residue_alpha_total`, the clamp at `P` is the outside of the target.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- west of a point of a side line is outside the target -/
theorem west_outside (S : SetupT D u v α β γ L ax ay) {ε x η : ℝ} (hε : ε = 1 ∨ ε = -1)
    (hside : (ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0) ∨
      (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0)) {δ : ℝ} (hδ : 0 < δ) :
    lpT (u : ℝ) (v : ℝ) ε x (0 - δ) η ∉ D.target.carrier := by
  intro hmem
  rcases hside with ⟨rfl, h0⟩ | ⟨rfl, h0⟩
  · have := S.bwd1T (ξ := 0) (η := η) hδ hmem
    linarith
  · have := S.bwdmT (ξ := 0) (η := η) hδ hmem
    linarith

/-- **From an `α`-tile with an edge on the row to `Δ` or a `b`-edge east.** -/
theorem row_alpha_tile (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η t0 : ℝ} {e1 : Fin N} {k m : Fin 3}
    (hkm : k ≠ m) (hk : (D.tile e1).pts k = lpT (u : ℝ) (v : ℝ) ε x ξ η) (ht0 : 0 < t0)
    (hm : (D.tile e1).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + t0) η)
    (hle : ∀ i, GHT (u : ℝ) (v : ℝ) ((D.tile e1).pts i) ≤ -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η))
    (hαk : (D.tile e1).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) = α) :
    UTT D (u : ℝ) (v : ℝ) ε x ξ η ∨ BEastT D (u : ℝ) (v : ℝ) ε x α ξ η := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hab := S.tile.hab
  have hac := S.tile.ac
  have hbc := S.tile.bc
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k m hkm
  have hkj : k ≠ j₃ := Ne.symm hjk
  have hmj : m ≠ j₃ := Ne.symm hjm
  have hang := angle_at_vertexT D hab hac hbc S.hM e1 hkm hkj hmj
  have hαk' : (D.tile e1).localAngle ((D.tile e1).pts k) = α := by rw [hk]; exact hαk
  have hdd : dist ((D.tile e1).pts k) ((D.tile e1).pts m) = t0 * ((u : ℝ) * v) := by
    rw [hk, hm, dist_rowT (a := ξ) (b := ξ + t0) hu huv hv2 hε (by linarith)]
    ring
  have hαβ := alpha_ne_beta S
  have hαγ := alpha_ne_gamma S
  have hc' : (0 : ℝ) < (u : ℝ) * v := mul_pos hu (hu.trans huv)
  rcases vertex_dist_casesT D S.hM e1 hkm with hl | hl | hl
  · exfalso
    rcases sides_of_a_edgeT D S.tile S.hM e1 hkm hkj hmj hl with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · have := hang.2.1 (by rw [dist_comm]; exact s2)
      rw [hαk'] at this; exact hαβ this
    · have := hang.2.2 (by rw [dist_comm]; exact s2)
      rw [hαk'] at this; exact hαγ this
  · right
    have ht : t0 = nuT (u : ℝ) (v : ℝ) := by
      have h1' : t0 * ((u : ℝ) * v) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by rw [← hdd]; exact hl
      have h2' := nuT_spec (v := (v : ℝ)) hu (hu.trans huv)
      apply mul_right_cancel₀ hc'.ne'
      rw [h1']; linarith [h2']
    refine ⟨e1, k, m, hkm, hk, ?_, hle, hαk⟩
    rw [hm, ht]
  · left
    have ht1 : t0 = 1 := by
      have : t0 * ((u : ℝ) * v) = 1 * ((u : ℝ) * v) := by rw [← hdd, hl, one_mul]
      exact mul_right_cancel₀ hc'.ne' this
    have hm1 : (D.tile e1).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η := by rw [hm, ht1]
    rcases sides_of_c_edgeT D S.tile S.hM e1 hkm hkj hmj hl with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · exfalso
      have := hang.2.1 (by rw [dist_comm]; exact s2)
      rw [hαk'] at this; exact hαβ this
    · exact ⟨e1, row_edge_UT S hε hkm hkj hmj hk hm1 hle s1 s2⟩

theorem sector_dichotomy_P (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ} (hη : 0 < η)
    (hPf : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ frontier D.target.carrier)
    (hPnv : lpT (u : ℝ) (v : ℝ) ε x 0 η ∉ Set.range D.target.pts)
    (hside : (ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0) ∨
      (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0))
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
  have hfP : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x 0 η) = c0 := GHT_lp _ _ _ _
  have hfQ : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x 1 η) = c0 := GHT_lp _ _ _ _
  have hfP' : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x (-1) η) = c0 := GHT_lp _ _ _ _
  have hPQ : lpT (u : ℝ) (v : ℝ) ε x 0 η ≠ lpT (u : ℝ) (v : ℝ) ε x 1 η :=
    lpT_ne_xi hu huv hv2 hε (by norm_num)
  have hP' : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (-1) η)
      (lpT (u : ℝ) (v : ℝ) ε x 1 η) := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [lineMap_lpT]
    exact lpT_congr (by ring) (by ring)
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
  have hout : ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (-1) η) (lpT (u : ℝ) (v : ℝ) ε x 0 η),
      y ∉ D.target.carrier := by
    intro y hy
    rw [openSegment_eq_image_lineMap] at hy
    obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
    rw [lineMap_lpT]
    have := west_outside S C.hε hside (δ := 1 - τ) (by linarith)
    rwa [show lpT (u : ℝ) (v : ℝ) ε x (-1 + τ * (0 - -1)) (η + τ * (η - η))
      = lpT (u : ℝ) (v : ℝ) ε x (0 - (1 - τ)) η from lpT_congr (by ring) (by ring)]
  obtain ⟨e, he, k, m, t0, hkm, hk, ht0, hm, hle, hedge, hdist⟩ :=
    next_tile D.toDissection (GHT (u : ℝ) (v : ℝ)) hF c0 hPQ hfP hfQ hfP' hP' hint hwall
      (fun e _ => not_straddles_of_outside D.toDissection hout e.1 e.2)
  have hm' : (D.tile e.1).pts m = lpT (u : ℝ) (v : ℝ) ε x (0 + t0) η := by
    rw [hm, lineMap_lpT]; exact lpT_congr (by ring) (by ring)
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e'] at h; exact h
  have hγpos : 0 < γ := by rw [S.hγ]; linarith [S.hα]
  -- both known tiles lie south of the row
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
  -- the angles of the known tiles at P
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
  have htot := Erdos634.PinPlumbing.pin_angle_sum D.toDissection hPf hPnv
  have hα' := residue_alpha_total D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr
    (S.hM.hα') (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α (Θ := Real.pi) (by have := S.hα; linarith) htot {tD, tN}
    (by rw [hsum]) e.1 (by simp [n1, n2]) hnz
  exact row_alpha_tile C hkm hk ht0 hm' hle hα'

#print axioms sector_dichotomy_P
end Erdos634.Draft.ThmDRun
