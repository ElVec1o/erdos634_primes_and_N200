import Mathlib.Tactic
import Erdos634.Draft.ThmDSector2
import Erdos634.Draft.ThmDRunNext
import Erdos634.Draft.ThmDRunRowA

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' (R5 sector step 3): the `α`-tile at an interior lattice vertex is `Δ` or has a `b`-edge running east  

`sector_dichotomy` : at `x = lp ξ η` interior to the target, with the five tiles of `sector_five_unique` present, either `Δ_{ξ,η}`
is a tile, or a tile north of the row `ℓ_η` has `α` at `x` and a `b`-edge on `ℓ_η` running east from `x`
(`BEastT`: the end is `lp (ξ + ν) η`, `ν = b/c`).  This is exactly the dichotomy "`G_j = Δ_{s-j,j}` or `G_j` has its `b` edge on
`ℓ_j` running east from `x(s-j,j)`" of Lemmas 32/33 (Beeson-Rosu pp. 27-29).  Route: `next_tile` along the `c`-edge of `∇_{ξ,η-1}`
(north side of the row, clamped by the `c`-edge of `Δ_{ξ-1,η}` via `clamp_b`), the tile found is none of the five (positions), so by
`sector_five_unique` its angle is `α`; the edge length is `b` or `c`; `c` gives `Δ` (`row_edge_UT`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- a tile north of the row `ℓ_η` with `α` at `lp ξ η` and a `b`-edge on `ℓ_η` running east from it -/
def BEastT (D : CongruentDissection N) (u v ε x α ξ η : ℝ) : Prop :=
  ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t).pts k = lpT u v ε x ξ η ∧
    (D.tile t).pts m = lpT u v ε x (ξ + nuT u v) η ∧
    (∀ i, GHT u v ((D.tile t).pts i) ≤ -((u * v) * hhT u v * η)) ∧
    (D.tile t).localAngle (lpT u v ε x ξ η) = α

theorem sector_dichotomy (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ}
    (hx : lpT (u : ℝ) (v : ℝ) ε x ξ η ∈ interior D.target.carrier)
    {t1 t2 t3 t4 t5 : Fin N}
    (h1 : HasV D t1 (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ η)
      (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) (η + 1)))
    (h2 : HasV D t2 (lpT (u : ℝ) (v : ℝ) ε x ξ (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1))
      (lpT (u : ℝ) (v : ℝ) ε x ξ η))
    (h3 : HasV D t3 (lpT (u : ℝ) (v : ℝ) ε x ξ (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x ξ η))
    (h4 : HasV D t4 (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) (η + 1))
      (lpT (u : ℝ) (v : ℝ) ε x ξ (η + 1)))
    (h5 : HasV D t5 (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) (η - 1)) (lpT (u : ℝ) (v : ℝ) ε x ξ η)
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η)) :
    UTT D (u : ℝ) (v : ℝ) ε x ξ η ∨ BEastT D (u : ℝ) (v : ℝ) ε x α ξ η := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hab := S.tile.hab
  have hac := S.tile.ac
  have hbc := S.tile.bc
  have hnh := nhT_pos hu huv hv2
  have hF : GHT (u : ℝ) (v : ℝ) ≠ 0 := GHT_ne hu huv
  set c0 : ℝ := -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η) with hc0
  have hfP : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x ξ η) = c0 := GHT_lp _ _ _ _
  have hfQ : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) = c0 := GHT_lp _ _ _ _
  have hfP' : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η) = c0 := GHT_lp _ _ _ _
  have hPQ : lpT (u : ℝ) (v : ℝ) ε x ξ η ≠ lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η :=
    lpT_ne_xi hu huv hv2 hε (by linarith)
  have hP' : lpT (u : ℝ) (v : ℝ) ε x ξ η ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η)
      (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [lineMap_lpT]
    exact lpT_congr (by ring) (by ring)
  have hQmem : lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η ∈ D.target.carrier := h5.mem₃
  have hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) ⊆
      interior D.target.carrier :=
    D.target.convex.openSegment_interior_closure_subset_interior hx (subset_closure hQmem)
  have hwall : ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x ξ η) (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h5
    refine seg_wall D.toDissection (t := t5) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  -- clamp: t1 has the row edge [P', P]
  have hclamp : ∀ e ∈ D.toDissection.lineChain (GHT (u : ℝ) (v : ℝ)) c0,
      ¬ Straddles ((D.tile e.1).edge e.2) (lpT (u : ℝ) (v : ℝ) ε x (ξ - 1) η) (lpT (u : ℝ) (v : ℝ) ε x ξ η)
        (lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η) := by
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := h1
    refine clamp_b D.toDissection (GHT (u : ℝ) (v : ℝ)) hF c0 hPQ hfP hfQ hfP' hP' hkm hk hm ?_
    refine HasV.all ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ (P := fun p => GHT (u : ℝ) (v : ℝ) p ≤ c0) ?_ ?_ ?_
    · exact hfP'.le
    · exact hfP.le
    · exact GHT_le hu huv hv2 (by linarith)
  obtain ⟨e, he, k, m, t0, hkm, hk, ht0, hm, hle, hedge, hdist⟩ :=
    next_tile D.toDissection (GHT (u : ℝ) (v : ℝ)) hF c0 hPQ hfP hfQ hfP' hP' hint hwall hclamp
  -- the tile found
  have hm' : (D.tile e.1).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + t0) η := by
    rw [hm, lineMap_lpT]; exact lpT_congr (by ring) (by ring)
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e'] at h; exact h
  have hγpos : 0 < γ := by rw [S.hγ]; linarith [S.hα]
  -- distinct from the five
  have n2 : e.1 ≠ t2 := by
    obtain ⟨k2, -, -, -, -, -, hk2, -, -⟩ := h2
    exact ne_of_F (D := D) (GHT (u : ℝ) (v : ℝ)) hle (i := k2)
      (by rw [hk2]; exact GHT_gt hu huv hv2 (by linarith))
  have n3 : e.1 ≠ t3 := by
    obtain ⟨k2, -, -, -, -, -, hk2, -, -⟩ := h3
    exact ne_of_F (D := D) (GHT (u : ℝ) (v : ℝ)) hle (i := k2)
      (by rw [hk2]; exact GHT_gt hu huv hv2 (by linarith))
  have n5 : e.1 ≠ t5 := by
    obtain ⟨k2, -, -, -, -, -, hk2, -, -⟩ := h5
    exact ne_of_F (D := D) (GHT (u : ℝ) (v : ℝ)) hle (i := k2)
      (by rw [hk2]; exact GHT_gt hu huv hv2 (by linarith))
  have n1 : e.1 ≠ t1 := by
    refine h1.ne_of_vertex hm' ?_ ?_ ?_
    · exact lpT_ne_xi hu huv hv2 hε (by linarith)
    · exact lpT_ne_xi hu huv hv2 hε (by linarith)
    · exact lpT_ne_eta hu huv hv2 (by linarith)
  have n4 : e.1 ≠ t4 := by
    refine h4.ne_of_vertex hm' ?_ ?_ ?_
    · exact lpT_ne_xi hu huv hv2 hε (by linarith)
    · exact lpT_ne_eta hu huv hv2 (by linarith)
    · exact lpT_ne_eta hu huv hv2 (by linarith)
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k m hkm
  have hkj : k ≠ j₃ := Ne.symm hjk
  have hmj : m ≠ j₃ := Ne.symm hjm
  have hang := angle_at_vertexT D hab hac hbc S.hM e.1 hkm hkj hmj
  have hop := vertex_dist_casesT D S.hM e.1 hmj
  have hnz : (D.tile e.1).localAngle (lpT (u : ℝ) (v : ℝ) ε x ξ η) ≠ 0 := by
    rw [← hk]
    rcases hop with h | h | h
    · rw [hang.1 h]; exact S.hα.ne'
    · rw [hang.2.1 h]; exact hβpos.ne'
    · rw [hang.2.2 h]; exact hγpos.ne'
  have hα' := sector_five_unique C hx h1 h2 h3 h4 h5 e.1 n1 n2 n3 n4 n5 hnz
  have hαk : (D.tile e.1).localAngle ((D.tile e.1).pts k) = α := by rw [hk]; exact hα'
  have hdd : dist ((D.tile e.1).pts k) ((D.tile e.1).pts m) = t0 * ((u : ℝ) * v) := by
    rw [hk, hm', dist_rowT (a := ξ) (b := ξ + t0) hu huv hv2 hε (by linarith)]
    ring
  have hαβ := alpha_ne_beta S
  have hαγ := alpha_ne_gamma S
  rcases vertex_dist_casesT D S.hM e.1 hkm with hl | hl | hl
  · -- an a-edge cannot start at an alpha vertex
    exfalso
    rcases sides_of_a_edgeT D S.tile S.hM e.1 hkm hkj hmj hl with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · have := hang.2.1 (by rw [dist_comm]; exact s2)
      rw [hαk] at this; exact hαβ this
    · have := hang.2.2 (by rw [dist_comm]; exact s2)
      rw [hαk] at this; exact hαγ this
  · -- a b-edge east
    right
    have hc' : (0 : ℝ) < (u : ℝ) * v := mul_pos hu (hu.trans huv)
    have ht : t0 = nuT (u : ℝ) (v : ℝ) := by
      have h1' : t0 * ((u : ℝ) * v) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by rw [← hdd]; exact hl
      have h2' := nuT_spec (v := (v : ℝ)) hu (hu.trans huv)
      apply mul_right_cancel₀ hc'.ne'
      rw [h1']; linarith [h2']
    refine ⟨e.1, k, m, hkm, hk, ?_, ?_, ?_⟩
    · rw [hm', ht]
    · intro i; have := hle i; rw [hc0] at *; exact this
    · rw [← hk]; exact hαk
  · -- a c-edge: the tile above the row is Delta
    left
    have ht1 : t0 = 1 := by
      have : t0 * ((u : ℝ) * v) = 1 * ((u : ℝ) * v) := by rw [← hdd, hl, one_mul]
      exact mul_right_cancel₀ (mul_pos hu (hu.trans huv)).ne' this
    have hm1 : (D.tile e.1).pts m = lpT (u : ℝ) (v : ℝ) ε x (ξ + 1) η := by rw [hm', ht1]
    rcases sides_of_c_edgeT D S.tile S.hM e.1 hkm hkj hmj hl with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · exfalso
      have := hang.2.1 (by rw [dist_comm]; exact s2)
      rw [hαk] at this; exact hαβ this
    · exact ⟨e.1, row_edge_UT S hε hkm hkj hmj hk hm1 hle s1 s2⟩

#print axioms sector_dichotomy
end Erdos634.Draft.ThmDRun
