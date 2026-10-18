import Mathlib.Tactic
import Erdos634.Draft.ThmDL32Col

/-!
# Theorem D' (Lemma 32, step B helpers): the north tile `T_N` at `R`  

* `vertex_angle_ne_zero` : a vertex of a tile has a nonzero local angle;
* `tN_facts` : for a north tile `T_N` with a row edge `[p,q]` containing `R = lp m0 r` in its interior: its angle at `R` is `π`, the
  extension of the diagonal beyond `R` (a short piece `lp (m0-θ) (r+θ)`, `θ > 0`) lies in its interior, and it has a vertex
  strictly west of the diagonal (`GST > -lv (m0 + r)`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem vertex_angle_ne_zero (S : SetupT D u v α β γ L ax ay) (i : Fin N) (k : Fin 3) :
    (D.tile i).localAngle ((D.tile i).pts k) ≠ 0 := by
  have hβpos : 0 < β := by
    have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
    have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
    rw [e'] at h; exact h
  have hγpos : 0 < γ := by rw [S.hγ]; linarith [S.hα]
  obtain ⟨m, hkm⟩ : ∃ m : Fin 3, k ≠ m := ⟨k + 1, (fin3_succ_ne k).2.1.symm⟩
  obtain ⟨j₃, hjk, hjm⟩ := fin3_third k m hkm
  have hang := angle_at_vertexT D S.tile.hab S.tile.ac S.tile.bc S.hM i hkm (Ne.symm hjk) (Ne.symm hjm)
  rcases vertex_dist_casesT D S.hM i (Ne.symm hjm) with h | h | h
  · rw [hang.1 h]; exact S.hα.ne'
  · rw [hang.2.1 h]; exact hβpos.ne'
  · rw [hang.2.2 h]; exact hγpos.ne'

/-- **The north tile `T_N` of Lemma 32.** -/
theorem tN_facts (C : CtxBaseT D u v α β γ L ax ay ε x) {r m0 : ℕ} (hr : 1 ≤ r) {tN : Fin N} {kN mN : Fin 3}
    (hkm : kN ≠ mN)
    (hk : GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts kN) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)))
    (hm : GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts mN) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)))
    (hle : ∀ i, GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts i) ≤ -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)))
    (hR : lpT (u : ℝ) (v : ℝ) ε x (m0 : ℝ) (r : ℝ) ∈ openSegment ℝ ((D.tile tN).pts kN) ((D.tile tN).pts mN)) :
    (D.tile tN).localAngle (lpT (u : ℝ) (v : ℝ) ε x (m0 : ℝ) (r : ℝ)) = Real.pi ∧
    (∃ θ : ℝ, 0 < θ ∧ ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) - θ) ((r : ℝ) + θ))
        (lpT (u : ℝ) (v : ℝ) ε x (m0 : ℝ) (r : ℝ)), y ∈ interior (D.tile tN).carrier) ∧
    (∃ iw ie : Fin 3, ∃ δ : ℝ, 0 < δ ∧
      -lvT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) + r) < GST (u : ℝ) (v : ℝ) ε ((D.tile tN).pts iw) ∧
      (D.tile tN).pts ie = lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) + δ) (r : ℝ)) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hF : GHT (u : ℝ) (v : ℝ) ≠ 0 := GHT_ne hu huv
  have hnh := nhT_pos hu huv hv2
  obtain ⟨-, hpi, hpush⟩ := edge_interior_push (D.tile tN) hkm (GHT (u : ℝ) (v : ℝ)) hF _ hk hm hle hR
  refine ⟨hpi, ?_, ?_⟩
  · -- the push direction `d = lp (m0-1) (r+1) - R`
    set R := lpT (u : ℝ) (v : ℝ) ε x (m0 : ℝ) (r : ℝ) with hRdef
    set d : Plane := lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) - 1) ((r : ℝ) + 1) - R with hd
    have hGd : GHT (u : ℝ) (v : ℝ) d < 0 := by
      rw [hd, map_sub, GHT_lp, hRdef, GHT_lp]
      nlinarith
    obtain ⟨ε0, hε0, hpush'⟩ := hpush d hGd
    refine ⟨ε0 / 2, by positivity, fun y hy => ?_⟩
    rw [openSegment_eq_image_lineMap] at hy
    obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
    have e : AffineMap.lineMap (lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) - ε0 / 2) ((r : ℝ) + ε0 / 2)) R τ
        = R + ((1 - τ) * (ε0 / 2)) • d := by
      rw [AffineMap.lineMap_apply]
      have hext : lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) - ε0 / 2) ((r : ℝ) + ε0 / 2) = R + (ε0 / 2) • d := by
        rw [hd, hRdef]
        have := lp_extT (u := (u : ℝ)) (v := (v : ℝ)) ε x (m0 : ℝ) (r : ℝ) ((m0 : ℝ) - 1) ((r : ℝ) + 1) (-(ε0 / 2))
        rw [show (m0 : ℝ) + -(ε0 / 2) * ((m0 : ℝ) - ((m0 : ℝ) - 1)) = (m0 : ℝ) - ε0 / 2 by ring,
          show (r : ℝ) + -(ε0 / 2) * ((r : ℝ) - ((r : ℝ) + 1)) = (r : ℝ) + ε0 / 2 by ring] at this
        rw [← this]
        module
      rw [hext]
      simp only [vsub_eq_sub, vadd_eq_add, smul_eq_mul]
      module
    rw [e]
    exact hpush' _ (by nlinarith) (by nlinarith)
  · -- a vertex of `T_N` west of the diagonal
    set p := (D.tile tN).pts kN with hp
    set q := (D.tile tN).pts mN with hq
    have ep := onRow_eq_lp (x := x) (η := (r : ℝ)) hu huv hv2 hε hk
    have eq' := onRow_eq_lp (x := x) (η := (r : ℝ)) hu huv hv2 hε hm
    set ξp := xiOf (u : ℝ) (v : ℝ) ε x (r : ℝ) p with hξp
    set ξq := xiOf (u : ℝ) (v : ℝ) ε x (r : ℝ) q with hξq
    have hpq : p ≠ q := fun h => hkm ((D.tile tN).indep.injective h)
    have hξne : ξp ≠ ξq := by
      intro h; apply hpq; rw [ep, eq', h]
    have hR' := hR
    rw [ep, eq'] at hR'
    obtain ⟨t, h1, h2, ht⟩ := row_seg_param (openSegment_subset_segment ℝ _ _ hR')
    have htm : t = (m0 : ℝ) := lpT_xi_eq hu huv hv2 hε ht.symm
    rw [htm] at h1 h2
    have hm0p : (m0 : ℝ) ≠ ξp := by
      intro h
      have : lpT (u : ℝ) (v : ℝ) ε x (m0 : ℝ) (r : ℝ) = p := by rw [h, ← ep]
      rw [this] at hR
      exact hpq (left_mem_openSegment_iff.mp hR)
    have hm0q : (m0 : ℝ) ≠ ξq := by
      intro h
      have : lpT (u : ℝ) (v : ℝ) ε x (m0 : ℝ) (r : ℝ) = q := by rw [h, ← eq']
      rw [this] at hR
      exact hpq (right_mem_openSegment_iff.mp hR)
    rcases lt_or_gt_of_ne hξne with hlt | hgt
    · rw [min_eq_left hlt.le] at h1
      rw [max_eq_right hlt.le] at h2
      have hξ : ξp < m0 := lt_of_le_of_ne h1 (Ne.symm hm0p)
      have hξ' : (m0 : ℝ) < ξq := lt_of_le_of_ne h2 hm0q
      refine ⟨kN, mN, ξq - m0, by linarith, ?_, ?_⟩
      · rw [← hp, ep, GST_lp hε]
        refine neg_lt_neg (lvT_lt hu huv hv2 ?_)
        linarith
      · rw [← hq, eq']
        exact lpT_congr (by ring) rfl
    · rw [min_eq_right hgt.le] at h1
      rw [max_eq_left hgt.le] at h2
      have hξ : ξq < m0 := lt_of_le_of_ne h1 (Ne.symm hm0q)
      have hξ' : (m0 : ℝ) < ξp := lt_of_le_of_ne h2 hm0p
      refine ⟨mN, kN, ξp - m0, by linarith, ?_, ?_⟩
      · rw [← hq, eq', GST_lp hε]
        refine neg_lt_neg (lvT_lt hu huv hv2 ?_)
        linarith
      · rw [← hp, ep]
        exact lpT_congr (by ring) rfl

#print axioms vertex_angle_ne_zero
end Erdos634.Draft.ThmDRun
