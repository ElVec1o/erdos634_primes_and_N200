import Mathlib.Tactic
import Erdos634.Draft.ThmDRowFarLat
import Erdos634.Draft.ThmDRunRowA
import Erdos634.RunPartition

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the trapezoid lemma for a stopped run (their Lemma 32, p. 26).
# Theorem D' (Lemma 32, 1D tools): points of a lattice row; no chain edge straddles an endpoint of a chain edge  

* `onRow_eq_lp` : a point on the row `GHT = -(c h η)` is `lp ξ η` with an explicit `ξ`;
* `row_seg_mem`, `row_seg_param` : segments between points of a row, in the coordinate `ξ`;
* `no_straddle_at_endpoint` : if a chain edge `e1` on the row has `P = lp ξP η` as an endpoint, no chain edge straddles `P`
  (two same-side chain edges meet in at most one point).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set

section row1
variable {u v : ℝ}

/-- the `ξ`-coordinate of a point of a row -/
noncomputable def xiOf (u v ε x η : ℝ) (p : Plane) : ℝ := (ε * (p 0 - x) + η * uuT u v) / (u * v) - η

theorem onRow_eq_lp {ε x η : ℝ} (hu : 0 < u) (huv : u < v) (hv : v < 2 * u) (hε : ε ^ 2 = 1) {p : Plane}
    (hp : GHT u v p = -((u * v) * hhT u v * η)) : p = lpT u v ε x (xiOf u v ε x η p) η := by
  have hh := hhT_pos hu huv hv
  have hc : 0 < u * v := mul_pos hu (hu.trans huv)
  rw [GHT_apply] at hp
  have hp1 : p 1 = η * hhT u v := by
    have : (u * v) * (p 1) = (u * v) * (η * hhT u v) := by linarith
    exact mul_left_cancel₀ hc.ne' this
  apply plane_ext
  · have hu0 : u ≠ 0 := hu.ne'
    have hv0 : v ≠ 0 := (hu.trans huv).ne'
    have hxi : (xiOf u v ε x η p + η) * (u * v) = ε * (p 0 - x) + η * uuT u v := by
      unfold xiOf; field_simp; ring
    unfold lpT
    rw [mkPt_zero]
    have : ((xiOf u v ε x η p + η) * (u * v) - η * uuT u v) = ε * (p 0 - x) := by linarith
    rw [this]
    linear_combination (-(p 0 - x)) * hε
  · unfold lpT
    rw [mkPt_one]; exact hp1

theorem row_seg_mem {ε x η a b t : ℝ} (hab : a ≠ b) (h1 : min a b ≤ t) (h2 : t ≤ max a b) :
    lpT u v ε x t η ∈ segment ℝ (lpT u v ε x a η) (lpT u v ε x b η) := by
  have hd : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have hτ : 0 ≤ (t - a) / (b - a) ∧ (t - a) / (b - a) ≤ 1 := by
    rcases lt_or_gt_of_ne hab with h | h
    · rw [min_eq_left h.le] at h1; rw [max_eq_right h.le] at h2
      have hpos : 0 < b - a := by linarith
      exact ⟨div_nonneg (by linarith) hpos.le, (div_le_one hpos).mpr (by linarith)⟩
    · rw [min_eq_right h.le] at h1; rw [max_eq_left h.le] at h2
      have hneg : b - a < 0 := by linarith
      exact ⟨div_nonneg_of_nonpos (by linarith) hneg.le, (div_le_one_of_neg hneg).mpr (by linarith)⟩
  have h := lp_mem_segT (u := u) (v := v) (ε := ε) (x := x) (ξ := a) (η := η) (ξ' := b) (η' := η)
    (τ := (t - a) / (b - a)) hτ.1 hτ.2
  have e1 : a + (t - a) / (b - a) * (b - a) = t := by field_simp; ring
  have e2 : η + (t - a) / (b - a) * (η - η) = η := by ring
  rw [e1, e2] at h; exact h

theorem row_seg_param {ε x η a b : ℝ} {y : Plane}
    (hy : y ∈ segment ℝ (lpT u v ε x a η) (lpT u v ε x b η)) :
    ∃ t, min a b ≤ t ∧ t ≤ max a b ∧ y = lpT u v ε x t η := by
  obtain ⟨τ, h0, h1, rfl⟩ := lp_seg_paramT hy
  refine ⟨a + τ * (b - a), ?_, ?_, lpT_congr rfl (by ring)⟩
  · rcases le_total a b with h | h
    · rw [min_eq_left h]; nlinarith
    · rw [min_eq_right h]; nlinarith
  · rcases le_total a b with h | h
    · rw [max_eq_right h]; nlinarith
    · rw [max_eq_left h]; nlinarith

end row1

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- the endpoints of a chain edge of a row, in lattice coordinates -/
theorem chain_edge_coords (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ} {e : Fin N × Fin 3}
    (he : e ∈ D.toDissection.lineChain (GHT (u : ℝ) (v : ℝ)) (-((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η))) :
    ∃ a b : ℝ, a ≠ b ∧ (D.tile e.1).pts e.2 = lpT (u : ℝ) (v : ℝ) ε x a η ∧
      (D.tile e.1).pts (e.2 + 1) = lpT (u : ℝ) (v : ℝ) ε x b η ∧
      (D.tile e.1).edge e.2 = segment ℝ (lpT (u : ℝ) (v : ℝ) ε x a η) (lpT (u : ℝ) (v : ℝ) ε x b η) := by
  have S := C.S
  obtain ⟨h1, h2, -⟩ := Dissection.mem_lineChain.mp he
  have hε := C.e2
  have e1 := onRow_eq_lp (x := x) (η := η) S.u0 S.uv' S.v2 hε h1
  have e2 := onRow_eq_lp (x := x) (η := η) S.u0 S.uv' S.v2 hε h2
  refine ⟨_, _, ?_, e1, e2, ?_⟩
  · intro hab
    have hne : (D.tile e.1).pts e.2 ≠ (D.tile e.1).pts (e.2 + 1) := fun h =>
      (fin3_succ_ne e.2).2.1 ((D.tile e.1).indep.injective h).symm
    apply hne
    rw [e1, e2, hab]
  · show segment ℝ ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = _
    exact congr (congrArg (segment ℝ) e1) e2

/-- **No chain edge straddles an endpoint of a chain edge of the same row.** -/
theorem no_straddle_at_endpoint (C : CtxBaseT D u v α β γ L ax ay ε x) {η ξP ξ' ξQ : ℝ}
    (hξ' : ξ' < ξP) (hξQ : ξP < ξQ) {e1 : Fin N × Fin 3}
    (he1 : e1 ∈ D.toDissection.lineChain (GHT (u : ℝ) (v : ℝ)) (-((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η)))
    (hend : (D.tile e1.1).pts e1.2 = lpT (u : ℝ) (v : ℝ) ε x ξP η ∨
      (D.tile e1.1).pts (e1.2 + 1) = lpT (u : ℝ) (v : ℝ) ε x ξP η)
    {e : Fin N × Fin 3}
    (he : e ∈ D.toDissection.lineChain (GHT (u : ℝ) (v : ℝ)) (-((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η))) :
    ¬ Straddles ((D.tile e.1).edge e.2) (lpT (u : ℝ) (v : ℝ) ε x ξ' η) (lpT (u : ℝ) (v : ℝ) ε x ξP η)
      (lpT (u : ℝ) (v : ℝ) ε x ξQ η) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hxi := fun {a b : ℝ} (h : lpT (u : ℝ) (v : ℝ) ε x a η = lpT (u : ℝ) (v : ℝ) ε x b η) =>
    lpT_xi_eq hu huv hv2 hε h
  rintro ⟨⟨y, hyE, hyP⟩, ⟨z, hzE, hzQ⟩⟩
  -- coordinates of y and z
  obtain ⟨ty, hty1, hty2, rfl⟩ := row_seg_param (openSegment_subset_segment ℝ _ _ hyP)
  obtain ⟨tz, htz1, htz2, rfl⟩ := row_seg_param (openSegment_subset_segment ℝ _ _ hzQ)
  rw [min_eq_left hξ'.le] at hty1
  rw [max_eq_right hξ'.le] at hty2
  rw [min_eq_left hξQ.le] at htz1
  rw [max_eq_right hξQ.le] at htz2
  have hty : ty < ξP := by
    rcases lt_or_eq_of_le hty2 with h | h
    · exact h
    · exfalso
      rw [h] at hyP
      exact absurd (right_mem_openSegment_iff.mp hyP) (lpT_ne_xi hu huv hv2 hε (by linarith))
  have htz : ξP < tz := by
    rcases lt_or_eq_of_le htz1 with h | h
    · exact h
    · exfalso
      rw [← h] at hzQ
      exact absurd (left_mem_openSegment_iff.mp hzQ) (lpT_ne_xi hu huv hv2 hε (by linarith))
  -- the two chain edges
  obtain ⟨a, b, hab, hpa, hqb, hedge⟩ := chain_edge_coords C he
  obtain ⟨a1, b1, hab1, hpa1, hqb1, hedge1⟩ := chain_edge_coords C he1
  have hyE' := hyE
  have hzE' := hzE
  rw [hedge] at hyE' hzE'
  obtain ⟨ty', hty'1, hty'2, hy'⟩ := row_seg_param hyE'
  obtain ⟨tz', htz'1, htz'2, hz'⟩ := row_seg_param hzE'
  have hty_eq : ty = ty' := hxi hy'
  have htz_eq : tz = tz' := hxi hz'
  rw [← hty_eq] at hty'1 hty'2
  rw [← htz_eq] at htz'1 htz'2
  -- the other endpoint of e1
  obtain ⟨ξ1, hξ1, he1seg⟩ : ∃ ξ1 : ℝ, ξ1 ≠ ξP ∧ (D.tile e1.1).edge e1.2 =
      segment ℝ (lpT (u : ℝ) (v : ℝ) ε x ξP η) (lpT (u : ℝ) (v : ℝ) ε x ξ1 η) := by
    rcases hend with h | h
    · rw [hpa1] at h
      have h' := hxi h
      refine ⟨b1, fun hb => hab1 (by rw [h', hb]), ?_⟩
      rw [hedge1, h']
    · rw [hqb1] at h
      have h' := hxi h
      refine ⟨a1, fun ha => hab1 (by rw [h', ha]), ?_⟩
      rw [hedge1, segment_symm, h']
  -- chain data for the subsingleton lemma
  obtain ⟨-, -, hle⟩ := Dissection.mem_lineChain.mp he
  obtain ⟨-, -, hle1⟩ := Dissection.mem_lineChain.mp he1
  have hss := fun hne : e ≠ e1 => D.toDissection.sameside_edges_subsingleton (GHT (u : ℝ) (v : ℝ))
    (-((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η)) (GHT_ne hu huv) hne
    ((D.tile e.1).carrier_subset_halfplane _ _ hle) ((D.tile e1.1).carrier_subset_halfplane _ _ hle1)
    (D.toDissection.lineChain_edge_subset he) (D.toDissection.lineChain_edge_subset he1)
  have hmem_e : ∀ t : ℝ, ty ≤ t → t ≤ tz → lpT (u : ℝ) (v : ℝ) ε x t η ∈ (D.tile e.1).edge e.2 := by
    intro t h1 h2
    rw [hedge]
    exact row_seg_mem hab (by linarith [hty'1]) (by linarith [htz'2])
  have hP_e : lpT (u : ℝ) (v : ℝ) ε x ξP η ∈ (D.tile e.1).edge e.2 := hmem_e ξP hty.le htz.le
  have hP_e1 : lpT (u : ℝ) (v : ℝ) ε x ξP η ∈ (D.tile e1.1).edge e1.2 := by
    rw [he1seg]; exact left_mem_segment ℝ _ _
  rcases lt_or_gt_of_ne hξ1 with hlt | hgt
  · -- the edge `e1` goes west
    have hne : e ≠ e1 := by
      intro h
      subst h
      rw [he1seg] at hzE
      obtain ⟨t2, h21, h22, h2e⟩ := row_seg_param hzE
      rw [min_eq_right hlt.le] at h21
      rw [max_eq_left hlt.le] at h22
      have := hxi h2e
      linarith
    set δ : ℝ := min (ξP - ξ1) (ξP - ty) / 2 with hδ
    have hδ0 : 0 < δ := by
      have : 0 < min (ξP - ξ1) (ξP - ty) := lt_min (by linarith) (by linarith)
      linarith
    have hm_e : lpT (u : ℝ) (v : ℝ) ε x (ξP - δ) η ∈ (D.tile e.1).edge e.2 :=
      hmem_e _ (by have := min_le_right (ξP - ξ1) (ξP - ty); linarith) (by linarith)
    have hm_e1 : lpT (u : ℝ) (v : ℝ) ε x (ξP - δ) η ∈ (D.tile e1.1).edge e1.2 := by
      rw [he1seg]
      exact row_seg_mem (Ne.symm hξ1) (by rw [min_eq_right hlt.le]
                                          have := min_le_left (ξP - ξ1) (ξP - ty); linarith)
        (by rw [max_eq_left hlt.le]; linarith)
    have := hss hne ⟨hm_e, hm_e1⟩ ⟨hP_e, hP_e1⟩
    have h2 := hxi this
    linarith
  · -- the edge `e1` goes east
    have hne : e ≠ e1 := by
      intro h
      subst h
      rw [he1seg] at hyE
      obtain ⟨t2, h21, h22, h2e⟩ := row_seg_param hyE
      rw [min_eq_left hgt.le] at h21
      rw [max_eq_right hgt.le] at h22
      have := hxi h2e
      linarith
    set δ : ℝ := min (ξ1 - ξP) (tz - ξP) / 2 with hδ
    have hδ0 : 0 < δ := by
      have : 0 < min (ξ1 - ξP) (tz - ξP) := lt_min (by linarith) (by linarith)
      linarith
    have hm_e : lpT (u : ℝ) (v : ℝ) ε x (ξP + δ) η ∈ (D.tile e.1).edge e.2 :=
      hmem_e _ (by linarith) (by have := min_le_right (ξ1 - ξP) (tz - ξP); linarith)
    have hm_e1 : lpT (u : ℝ) (v : ℝ) ε x (ξP + δ) η ∈ (D.tile e1.1).edge e1.2 := by
      rw [he1seg]
      exact row_seg_mem hξ1.symm (by rw [min_eq_left hgt.le]; linarith)
        (by rw [max_eq_right hgt.le]
            have := min_le_left (ξ1 - ξP) (tz - ξP); linarith)
    have := hss hne ⟨hm_e, hm_e1⟩ ⟨hP_e, hP_e1⟩
    have h2 := hxi this
    linarith

#print axioms no_straddle_at_endpoint
end Erdos634.Draft.ThmDRun
