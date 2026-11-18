/-
Draft/WGapSig6.lean -- written 16 November 2026 (session 8).  UNAUDITED beyond internal checks; hand proof WGAP_PROOF_2026-11-15 (P7.5 (b2)/(b3)).
Not imported by any aggregate.  No sorry, no native_decide.
`row_stepS` = `SideRunG.CtxBase.row_stepG` (a verbatim copy of its proof) with ONE extra conjunct in the "bad" branch: the edge of the bad tile on the row from `p(ρ,ζ+1)` has
length `a` (`t f² = e f`) or `c` (`t = 1`) (the length `b` is excluded by `hnob`, as in the original proof).
-/
import Erdos634.Draft.WGapSig5

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

section sig6

variable {e f : ℕ} {α β γ L ax ay ε x : ℝ}

theorem row_stepS (C : CtxBase D e f α β γ L ax ay ε x) {ρ ζ : ℝ} {tD : Fin N}
    (hDt : HasV D tD (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) ζ) (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)))
    (hζ : 0 ≤ ζ)
    (hcl : ∃ P' : Plane, GHG (f : ℝ) P' = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)) ∧
      lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ∈ openSegment ℝ P' (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) ∧
      ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1))),
        ¬ Straddles ((D.tile ed.1).edge ed.2) P' (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)))
    (hnob : ∀ ed ∈ D.lineChain (GHG (f : ℝ)) (-(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1))),
      (D.tile ed.1).edge ed.2 ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) →
      dist ((D.tile ed.1).pts ed.2) ((D.tile ed.1).pts (ed.2 + 1)) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2) :
    UTG D (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ∨
    ∃ (ix : Fin N) (k m j₃ : Fin 3) (t : ℝ), k ≠ m ∧ k ≠ j₃ ∧ m ≠ j₃ ∧
      (D.tile ix).pts k = lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ∧ 0 < t ∧ (D.tile ix).pts m = lpG (e : ℝ) (f : ℝ) ε x (ρ + t) (ζ + 1) ∧
      (∀ i, GHG (f : ℝ) ((D.tile ix).pts i) ≤ -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1))) ∧
      ((D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = β ∨ (D.tile ix).localAngle (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = γ) ∧
      (∀ i, (D.tile ix).pts i = lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1) → False) ∧ (t * (f : ℝ) ^ 2 = (e : ℝ) * f ∨ t = 1) := by
  have S := C.S
  have hε := C.e2
  have he0 := S.e0
  have hef := S.hef'
  have hf0 := S.f0
  have hc := S.c_pos
  have hVW : lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1) ≠ lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1) := lpG_ne_xi he0 hef hε (by linarith)
  have hfV : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)) := GHG_lp _ _ _ _ _ _
  have hfW : GHG (f : ℝ) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) = -(((f : ℝ) ^ 2 * hhG (e : ℝ) (f : ℝ)) * (ζ + 1)) := GHG_lp _ _ _ _ _ _
  have hint : openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) ⊆ interior D.target.carrier := by
    refine C.seg_intG hDt.mem₂ hDt.mem₃ (Or.inl (by linarith)) (Or.inl ⟨1, one_pos, hDt.mem₃⟩)
      (Or.inr ⟨1, one_pos, ?_⟩)
    rw [show ρ + 1 - 1 = ρ by ring]; exact hDt.mem₂
  have hwall : ∀ y ∈ openSegment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)),
      ∀ i, y ∉ interior (D.tile i).carrier := by
    intro y hy
    obtain ⟨k, m, j, hkm, hkj, hmj, hk, hm, hj⟩ := hDt
    refine seg_wall D.toDissection (t := tD) hmj ?_
    rw [hm, hj]; exact openSegment_subset_segment ℝ _ _ hy
  obtain ⟨P', hfP', hP', hP⟩ := hcl
  obtain ⟨ed, he, k, m, t, hkm, hk, ht, hm0, hle, hedge, hdist⟩ :=
    next_tile D.toDissection (GHG (f : ℝ)) (GHG_ne he0 hef) _ hVW hfV hfW hfP' hP' hint hwall hP
  have hm : (D.tile ed.1).pts m = lpG (e : ℝ) (f : ℝ) ε x (ρ + t) (ζ + 1) := by
    rw [hm0, lineMap_lpG]; exact lpG_congr (by ring) (by ring)
  have hd : dist ((D.tile ed.1).pts k) ((D.tile ed.1).pts m) = t * (f : ℝ) ^ 2 := by
    rw [hk, hm]
    exact dist_lpG he0 hef hε (by positivity) (by unfold QfG; ring)
  have hlam := vertex_dist_casesG D S.hM ed.1 hkm
  have hea : (e : ℝ) * (f : ℝ) < (f : ℝ) ^ 2 := by nlinarith [mul_pos hf0 (sub_pos.mpr hef)]
  have heb : (f : ℝ) ^ 2 - (e : ℝ) ^ 2 < (f : ℝ) ^ 2 := by nlinarith [mul_pos he0 he0]
  have ht1 : t ≤ 1 := by
    by_contra hgt
    rw [not_le] at hgt
    have h1 : (f : ℝ) ^ 2 < t * (f : ℝ) ^ 2 := by nlinarith [mul_pos (sub_pos.mpr hgt) hc]
    rcases hlam with h | h | h <;> rw [hd] at h <;> linarith
  have hsub : (D.tile ed.1).edge ed.2
      ⊆ segment ℝ (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) := by
    rw [hedge]
    refine (convex_segment _ _).segment_subset (left_mem_segment ℝ _ _) ?_
    rw [segment_eq_image_lineMap]
    exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩
  have hlamb : dist ((D.tile ed.1).pts k) ((D.tile ed.1).pts m) ≠ (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
    have h1 := hnob ed he hsub
    rw [hdist] at h1
    rw [hk, hm0]; exact h1
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k m hkm
  have hkj : k ≠ j₃ := Ne.symm hjk
  have hmj : m ≠ j₃ := Ne.symm hjm
  have hGV : dist (lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1)) (lpG (e : ℝ) (f : ℝ) ε x ρ (ζ + 1)) = (e : ℝ) * (f : ℝ) :=
    dist_lpG he0 hef hε (mul_pos he0 hf0).le (by unfold QfG; ring)
  have hGW : dist (lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1)) (lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1)) ^ 2
      = (f : ℝ) ^ 4 + 4 * (f : ℝ) ^ 2 * (e : ℝ) ^ 2 - (e : ℝ) ^ 4 := by
    rw [dist_lpG_sq he0 hef hε]; unfold QfG; ring
  have hA := angle_at_vertexG D S.tile S.hM ed.1 hkm hkj hmj
  rw [hk] at hA
  have hno_km : ∀ i, i = k ∨ i = m → (D.tile ed.1).pts i = lpG (e : ℝ) (f : ℝ) ε x (ρ - 1) (ζ + 1 + 1) → False := by
    intro i hi hpi
    rcases hi with rfl | rfl
    · rw [hk] at hpi
      have := lpG_eta_eq he0 hef hpi
      linarith
    · rw [hm] at hpi
      have := lpG_eta_eq he0 hef hpi
      linarith
  rcases hlam with h | h | h
  · -- an `a`-edge
    right
    rcases sides_of_a_edgeG D S.tile S.hM ed.1 hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · refine ⟨ed.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inl (hA.2.1 (by rw [dist_comm]; exact s2)), fun i hpi => ?_, Or.inl (by rw [← hd]; exact h)⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hk, hGV] at s1
        exact S.tile.ac s1
    · refine ⟨ed.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inr (hA.2.2 (by rw [dist_comm]; exact s2)), fun i hpi => ?_, Or.inl (by rw [← hd]; exact h)⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hk, hGV] at s1
        exact S.tile.hab s1
  · exact absurd h hlamb
  · -- a `c`-edge
    have ht1' : t = 1 := by
      have h1 : t * (f : ℝ) ^ 2 = 1 * (f : ℝ) ^ 2 := by rw [one_mul, ← hd, h]
      exact mul_right_cancel₀ hc.ne' h1
    have hmW : (D.tile ed.1).pts m = lpG (e : ℝ) (f : ℝ) ε x (ρ + 1) (ζ + 1) := by rw [hm, ht1']
    rcases sides_of_c_edgeG D S.tile S.hM ed.1 hkm hkj hmj h with ⟨s1, s2⟩ | ⟨s1, s2⟩
    · right
      refine ⟨ed.1, k, m, j₃, t, hkm, hkj, hmj, hk, ht, hm, hle,
        Or.inl (hA.2.1 (by rw [dist_comm]; exact s2)), fun i hpi => ?_, Or.inr ht1'⟩
      rcases fin3_cover k m j₃ hkm hkj hmj i with hi | hi | hi
      · exact hno_km i (Or.inl hi) hpi
      · exact hno_km i (Or.inr hi) hpi
      · rw [hi] at hpi
        rw [hpi, hmW] at s2
        rw [s2] at hGW
        have h3 : (e : ℝ) ^ 2 * ((e : ℝ) ^ 2 - 3 * (f : ℝ) ^ 2) = 0 := by linear_combination (1 / 2 : ℝ) * hGW
        have h4 : (e : ℝ) ^ 2 - 3 * (f : ℝ) ^ 2 = 0 :=
          (mul_eq_zero.mp h3).resolve_left (pow_pos he0 2).ne'
        nlinarith [mul_pos (sub_pos.mpr hef) (add_pos he0 hf0), mul_pos hf0 hf0]
    · left
      exact ⟨ed.1, row_edge_UG S hε hkm hkj hmj hk hmW hle s1 s2⟩


end sig6

#print axioms row_stepS

end Erdos634.Draft.WGapStmt
