import Mathlib.Tactic
import Erdos634.Draft.ThmDL32A
import Erdos634.Draft.ThmDRunRep
import Erdos634.Draft.ThmDRunFrame2
import Erdos634.Draft.ThmDPRow

/-!
# Theorem D' (Lemma 32, step A): `R` is interior to a north chain edge  
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem L32_A_gen (C : CtxBaseT D u v α β γ L ax ay ε x) {n s r i0 : ℕ} (hnv : n < v) (h1r : 1 ≤ r) (hrs : r < s)
    (hsn : s ≤ n) (hi0 : i0 + r < s) (Tt : TrapT D (u : ℝ) (v : ℝ) ε x s r)
    (hB : BEastT D (u : ℝ) (v : ℝ) ε x α (i0 : ℝ) (r : ℝ))
    (hPRw : PRow D (u : ℝ) (v : ℝ) ε x (r : ℝ)) :
    ∃ (tN : Fin N) (k m : Fin 3), k ≠ m ∧
      GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts k) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)) ∧
      GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts m) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)) ∧
      (∀ i, GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts i) ≤ -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ))) ∧
      lpT (u : ℝ) (v : ℝ) ε x (((s - r : ℕ) : ℝ)) (r : ℝ) ∈
        openSegment ℝ ((D.tile tN).pts k) ((D.tile tN).pts m) := by
  by_contra hno
  push_neg at hno
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hh := hhT_pos hu huv hv2
  have hc : (0 : ℝ) < (u : ℝ) * v := mul_pos hu (hu.trans huv)
  set η : ℝ := (r : ℝ) with hη
  have hη0 : 0 < η := by rw [hη]; exact_mod_cast (by omega : 0 < r)
  set m0 : ℕ := s - r with hm0def
  have hm0 : 1 ≤ m0 := by omega
  have hm0v : m0 < v := by omega
  have hm0R : (1 : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast hm0
  set c0 : ℝ := -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * η) with hc0
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 η with hPdef
  set R := lpT (u : ℝ) (v : ℝ) ε x (m0 : ℝ) η with hRdef
  have hF : GHT (u : ℝ) (v : ℝ) ≠ 0 := GHT_ne hu huv
  have hPR : P ≠ R := lpT_ne_xi hu huv hv2 hε (by linarith)
  have hfP : GHT (u : ℝ) (v : ℝ) P = c0 := GHT_lp _ _ _ _
  have hfR : GHT (u : ℝ) (v : ℝ) R = c0 := GHT_lp _ _ _ _
  have hS : segment ℝ P R ⊆ {y | GHT (u : ℝ) (v : ℝ) y = c0} :=
    Erdos634.RunPartition.CSlot.segment_subset_level _ _ hfP hfR
  -- the nabla tiles below the row
  have hnab : ∀ i : ℕ, i < m0 → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (η - 1))
      (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) η) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) η) :=
    fun i hi => trap_nabla Tt h1r (by omega)
  have hPmem : P ∈ D.target.carrier := hPRw.mem
  have hRmem : R ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hnab (m0 - 1) (by omega)
    have e : ((m0 - 1 : ℕ) : ℝ) + 1 = (m0 : ℝ) := by rw [Nat.cast_sub hm0]; simp
    have := ht.mem₃
    rwa [e] at this
  have h1mem : lpT (u : ℝ) (v : ℝ) ε x (0 + 1) η ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hnab 0 (by omega)
    have := ht.mem₃
    rwa [show ((0 : ℕ) : ℝ) + 1 = 0 + 1 by simp] at this
  have hm1mem : lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) - 1) η ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := hnab (m0 - 1) (by omega)
    have e : ((m0 - 1 : ℕ) : ℝ) = (m0 : ℝ) - 1 := by rw [Nat.cast_sub hm0]; simp
    have := ht.mem₂
    rwa [e] at this
  have hint : openSegment ℝ P R ⊆ interior D.target.carrier :=
    C.seg_intT hPmem hRmem (Or.inl hη0) (Or.inl ⟨1, one_pos, h1mem⟩) (Or.inr ⟨1, one_pos, hm1mem⟩)
  have hwall : ∀ y ∈ openSegment ℝ P R, ∀ j, y ∉ interior (D.tile j).carrier := by
    intro y hy j
    have hys : y ∈ segment ℝ P R := openSegment_subset_segment ℝ P R hy
    have hRe : R = lpT (u : ℝ) (v : ℝ) ε x (0 + (m0 : ℝ) * 1) (η + (m0 : ℝ) * 0) := lpT_congr (by ring) (by ring)
    rw [hRe] at hys
    obtain ⟨i, hi, hyi⟩ := seg_split_lpT (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (ξ := 0) (η := η)
      (dξ := 1) (dη := 0) (q := m0) hm0 hys
    obtain ⟨t, ht⟩ := hnab i hi
    obtain ⟨k, m, j', hkm, hkj, hmj, hk, hm, hj⟩ := ht
    have hseg : y ∈ segment ℝ ((D.tile t).pts m) ((D.tile t).pts j') := by
      rw [hm, hj]
      have e1 : lpT (u : ℝ) (v : ℝ) ε x (0 + (i : ℝ) * 1) (η + (i : ℝ) * 0) = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) η :=
        lpT_congr (by ring) (by ring)
      have e2 : lpT (u : ℝ) (v : ℝ) ε x (0 + ((i : ℝ) + 1) * 1) (η + ((i : ℝ) + 1) * 0)
          = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) η := lpT_congr (by ring) (by ring)
      rw [e1, e2] at hyi
      exact hyi
    exact seg_wall D.toDissection hmj hseg j
  -- the end `R` lies on a chain edge
  obtain ⟨ER, hER, hRER⟩ := endpoint_in_chain D.toDissection (GHT (u : ℝ) (v : ℝ)) hF c0 hPR hS hint hwall
  obtain ⟨a, b, hab, hpa, hqb, hedge⟩ := chain_edge_coords C hER
  obtain ⟨hER1, hER2, hERle⟩ := Dissection.mem_lineChain.mp hER
  have hRER' := hRER
  rw [hedge] at hRER'
  obtain ⟨tR, htR1, htR2, htR⟩ := row_seg_param hRER'
  have htRm : tR = (m0 : ℝ) := lpT_xi_eq hu huv hv2 hε htR.symm
  rw [htRm] at htR1 htR2
  by_cases hend : (m0 : ℝ) = a ∨ (m0 : ℝ) = b
  · -- `R` is an endpoint of the chain edge `ER`: contradiction with the window `RC`
    exfalso
    have hendER : (D.tile ER.1).pts ER.2 = R ∨ (D.tile ER.1).pts (ER.2 + 1) = R := by
      rcases hend with h | h
      · left; rw [hpa, ← h]
      · right; rw [hqb, ← h]
    set R' := lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) + 1) η with hR'def
    obtain ⟨s0, hs0, hcl⟩ := hPRw.rowclamp
    set P' := lpT (u : ℝ) (v : ℝ) ε x (-s0) η with hP'def
    have hstrR : ∀ e ∈ D.toDissection.lineChain (GHT (u : ℝ) (v : ℝ)) c0,
        ¬ Straddles ((D.tile e.1).edge e.2) R' R P := by
      intro e he
      rw [straddles_symm]
      exact no_straddle_at_endpoint C (by linarith : (0 : ℝ) < m0) (by linarith : (m0 : ℝ) < m0 + 1) hER hendER he
    have hstrP : ∀ e ∈ D.toDissection.lineChain (GHT (u : ℝ) (v : ℝ)) c0,
        ¬ Straddles ((D.tile e.1).edge e.2) P' P R := fun e _ => hcl R e.1 e.2
    have hfP' : GHT (u : ℝ) (v : ℝ) P' = c0 := GHT_lp _ _ _ _
    have hfR' : GHT (u : ℝ) (v : ℝ) R' = c0 := GHT_lp _ _ _ _
    have hm0p : (0 : ℝ) < (m0 : ℝ) + 1 := by linarith
    have hP'm : P ∈ openSegment ℝ P' R := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨s0 / ((m0 : ℝ) + s0), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_one (by positivity)]; linarith
      · rw [hP'def, hRdef, lineMap_lpT, hPdef]
        refine lpT_congr ?_ (by ring)
        field_simp; ring
    have hR'm : R ∈ openSegment ℝ P R' := by
      rw [openSegment_eq_image_lineMap]
      refine ⟨(m0 : ℝ) / ((m0 : ℝ) + 1), ⟨by positivity, ?_⟩, ?_⟩
      · rw [div_lt_one hm0p]; linarith
      · rw [hR'def, hPdef, hRdef, lineMap_lpT]
        refine lpT_congr ?_ (by ring)
        field_simp; ring
    have hrun := run_partition D.toDissection (GHT (u : ℝ) (v : ℝ)) hF c0 hPR hfP' hfR' hP'm hR'm hS hint hwall
      hstrP hstrR
    -- the `b`-edge running east
    obtain ⟨tb, kb, mb, hkmb, hkb, hmb, hleb, hαb⟩ := hB
    have hν0 : 0 < nuT (u : ℝ) (v : ℝ) := nuT_pos hu huv
    obtain ⟨e0, he0, hedge0, hdist0⟩ : ∃ e0 ∈ D.toDissection.lineChain (GHT (u : ℝ) (v : ℝ)) c0,
        (D.tile e0.1).edge e0.2 = segment ℝ (lpT (u : ℝ) (v : ℝ) ε x (i0 : ℝ) η)
          (lpT (u : ℝ) (v : ℝ) ε x ((i0 : ℝ) + nuT (u : ℝ) (v : ℝ)) η) ∧
        dist ((D.tile e0.1).pts e0.2) ((D.tile e0.1).pts (e0.2 + 1)) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
      have hdb : dist (lpT (u : ℝ) (v : ℝ) ε x (i0 : ℝ) η)
          (lpT (u : ℝ) (v : ℝ) ε x ((i0 : ℝ) + nuT (u : ℝ) (v : ℝ)) η) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
        rw [dist_rowT (a := (i0 : ℝ)) (b := (i0 : ℝ) + nuT (u : ℝ) (v : ℝ)) hu huv hv2 hε (by linarith)]
        have := nuT_spec (v := (v : ℝ)) hu (hu.trans huv)
        linarith
      have hg1 : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x (i0 : ℝ) η) = c0 := GHT_lp _ _ _ _
      have hg2 : GHT (u : ℝ) (v : ℝ) (lpT (u : ℝ) (v : ℝ) ε x ((i0 : ℝ) + nuT (u : ℝ) (v : ℝ)) η) = c0 :=
        GHT_lp _ _ _ _
      rcases pair_index kb mb hkmb with h | h
      · refine ⟨(tb, kb), Dissection.mem_lineChain.mpr ⟨?_, ?_, hleb⟩, ?_, ?_⟩
        · show GHT (u : ℝ) (v : ℝ) ((D.tile tb).pts kb) = c0
          rw [hkb]; exact hg1
        · show GHT (u : ℝ) (v : ℝ) ((D.tile tb).pts (kb + 1)) = c0
          rw [← h, hmb]; exact hg2
        · show segment ℝ ((D.tile tb).pts kb) ((D.tile tb).pts (kb + 1)) = _
          rw [← h, hkb, hmb]
        · show dist ((D.tile tb).pts kb) ((D.tile tb).pts (kb + 1)) = _
          rw [← h, hkb, hmb]; exact hdb
      · refine ⟨(tb, mb), Dissection.mem_lineChain.mpr ⟨?_, ?_, hleb⟩, ?_, ?_⟩
        · show GHT (u : ℝ) (v : ℝ) ((D.tile tb).pts mb) = c0
          rw [hmb]; exact hg2
        · show GHT (u : ℝ) (v : ℝ) ((D.tile tb).pts (mb + 1)) = c0
          rw [← h, hkb]; exact hg1
        · show segment ℝ ((D.tile tb).pts mb) ((D.tile tb).pts (mb + 1)) = _
          rw [← h, hkb, hmb, segment_symm]
        · show dist ((D.tile tb).pts mb) ((D.tile tb).pts (mb + 1)) = _
          rw [← h, hkb, hmb, dist_comm]; exact hdb
    -- the edge `e0` stays west of `R`
    have hi0R : (i0 : ℝ) + 1 ≤ m0 := by
      have : i0 + 1 ≤ m0 := by omega
      exact_mod_cast this
    have hi0nn : (0 : ℝ) ≤ i0 := Nat.cast_nonneg i0
    have hνle : (i0 : ℝ) + nuT (u : ℝ) (v : ℝ) ≤ m0 := by
      by_contra hlt
      push_neg at hlt
      apply hstrR e0 he0
      rw [hedge0]
      set δ : ℝ := min 1 ((i0 : ℝ) + nuT (u : ℝ) (v : ℝ) - m0) / 2 with hδ
      have hδpos : 0 < min 1 ((i0 : ℝ) + nuT (u : ℝ) (v : ℝ) - m0) := lt_min one_pos (by linarith)
      have hδ1 : min 1 ((i0 : ℝ) + nuT (u : ℝ) (v : ℝ) - m0) ≤ 1 := min_le_left _ _
      have hδ2 : min 1 ((i0 : ℝ) + nuT (u : ℝ) (v : ℝ) - m0) ≤ (i0 : ℝ) + nuT (u : ℝ) (v : ℝ) - m0 := min_le_right _ _
      have hi0lt : (i0 : ℝ) < (i0 : ℝ) + nuT (u : ℝ) (v : ℝ) := by linarith
      refine ⟨⟨lpT (u : ℝ) (v : ℝ) ε x ((m0 : ℝ) + δ) η, ?_, ?_⟩,
        ⟨lpT (u : ℝ) (v : ℝ) ε x (((i0 : ℝ) + m0) / 2) η, ?_, ?_⟩⟩
      · exact row_seg_mem (ne_of_lt hi0lt) (by rw [min_eq_left hi0lt.le]; linarith)
          (by rw [max_eq_right hi0lt.le]; linarith)
      · refine mem_openSegment_of_ne_left_right ?_ ?_ ?_
        · exact lpT_ne_xi hu huv hv2 hε (by linarith)
        · exact lpT_ne_xi hu huv hv2 hε (by linarith)
        · exact row_seg_mem (by linarith) (by rw [min_eq_right (by linarith)]; linarith)
            (by rw [max_eq_left (by linarith)]; linarith)
      · exact row_seg_mem (ne_of_lt hi0lt) (by rw [min_eq_left hi0lt.le]; linarith)
          (by rw [max_eq_right hi0lt.le]; linarith)
      · refine mem_openSegment_of_ne_left_right ?_ ?_ ?_
        · exact lpT_ne_xi hu huv hv2 hε (by linarith)
        · exact lpT_ne_xi hu huv hv2 hε (by linarith)
        · exact row_seg_mem (by linarith) (by rw [min_eq_right (by linarith)]; linarith)
            (by rw [max_eq_left (by linarith)]; linarith)
    have hsub0 : (D.tile e0.1).edge e0.2 ⊆ segment ℝ P R := by
      rw [hedge0]
      refine (convex_segment P R).segment_subset ?_ ?_
      · exact row_seg_mem (by linarith) (by rw [min_eq_left (by linarith)]; linarith)
          (by rw [max_eq_right (by linarith)]; linarith)
      · exact row_seg_mem (by linarith) (by rw [min_eq_left (by linarith)]; linarith)
          (by rw [max_eq_right (by linarith)]; linarith)
    obtain ⟨x', y', z', hxyz⟩ := Erdos634.Draft.W2E1.sum_split_semigroup _
      (fun e : Fin N × Fin 3 => dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)))
      ((u : ℝ) ^ 2) ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) ((u : ℝ) * v)
      (dist P R) (fun e _ => edge_length_casesT D S.hM e.1 e.2)
      (Finset.mem_filter.mpr ⟨he0, hsub0⟩) hrun
    have hdPR : dist P R = (m0 : ℝ) * ((u : ℝ) * v) := by
      rw [hPdef, hRdef, dist_rowT (a := 0) (b := (m0 : ℝ)) hu huv hv2 hε (by linarith)]
      ring
    rw [hdist0, hdPR] at hxyz
    have hreal : (x' : ℝ) * (u : ℝ) ^ 2 + (((y' + 1 : ℕ) : ℝ)) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + (z' : ℝ) * ((u : ℝ) * v)
        = (m0 : ℝ) * ((u : ℝ) * v) := by
      push_cast; linarith
    have := (chord_c S.hco S.hu S.huv (x := x') (y := y' + 1) (z := z') (j := m0) hreal).1 hm0v
    omega
  · -- `R` is in the relative interior of the chain edge
    push_neg at hend
    apply hno ER.1 ER.2 (ER.2 + 1) ((fin3_succ_ne ER.2).2.1.symm) hER1 hER2 hERle
    rw [hpa, hqb]
    refine mem_openSegment_of_ne_left_right ?_ ?_ ?_
    · exact lpT_ne_xi hu huv hv2 hε (Ne.symm hend.1)
    · exact lpT_ne_xi hu huv hv2 hε (Ne.symm hend.2)
    · rw [← hedge]; exact hRER

theorem L32_A (C : CtxBaseT D u v α β γ L ax ay ε x) {n s r i0 : ℕ} (hnv : n < v) (h1r : 1 ≤ r) (hrs : r < s)
    (hsn : s ≤ n) (hi0 : i0 + r < s) (Tt : TrapT D (u : ℝ) (v : ℝ) ε x s r)
    (hB : BEastT D (u : ℝ) (v : ℝ) ε x α (i0 : ℝ) (r : ℝ))
    (hPf : lpT (u : ℝ) (v : ℝ) ε x 0 (r : ℝ) ∈ frontier D.target.carrier ∧
      lpT (u : ℝ) (v : ℝ) ε x 0 (r : ℝ) ∉ Set.range D.target.pts ∧
      ((ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (r : ℝ)) = 0) ∨
        (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 (r : ℝ)) = 0))) :
    ∃ (tN : Fin N) (k m : Fin 3), k ≠ m ∧
      GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts k) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)) ∧
      GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts m) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)) ∧
      (∀ i, GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts i) ≤ -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ))) ∧
      lpT (u : ℝ) (v : ℝ) ε x (((s - r : ℕ) : ℝ)) (r : ℝ) ∈
        openSegment ℝ ((D.tile tN).pts k) ((D.tile tN).pts m) :=
  L32_A_gen C hnv h1r hrs hsn hi0 Tt hB (PRow_of_frontier C hPf.1 hPf.2.2)

#print axioms L32_A_gen
#print axioms L32_A
end Erdos634.Draft.ThmDRun
