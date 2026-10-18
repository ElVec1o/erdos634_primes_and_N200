import Mathlib.Tactic
import Erdos634.Draft.ThmDL32Col2

/-!
# Theorem D' (Lemma 32, step B): the column of `∇`'s east of `σ`  
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem L32_B (C : CtxBaseT D u v α β γ L ax ay ε x) {n s r : ℕ} (hnv : n < v) (hr : 1 ≤ r) (hrs : r < s)
    (hsn : s ≤ n) (Tt : TrapT D (u : ℝ) (v : ℝ) ε x s r)
    (hN : ∃ (tN : Fin N) (kN mN : Fin 3), kN ≠ mN ∧
      GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts kN) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)) ∧
      GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts mN) = -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ)) ∧
      (∀ i, GHT (u : ℝ) (v : ℝ) ((D.tile tN).pts i) ≤ -((u : ℝ) * v * hhT (u : ℝ) (v : ℝ) * (r : ℝ))) ∧
      lpT (u : ℝ) (v : ℝ) ε x (((s - r : ℕ) : ℝ)) (r : ℝ) ∈
        openSegment ℝ ((D.tile tN).pts kN) ((D.tile tN).pts mN)) :
    (∀ j : ℕ, j < r → DTT D (u : ℝ) (v : ℝ) ε x ((s - 1 - j : ℕ) : ℝ) (j : ℝ)) ∧
    openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (((s - r : ℕ) : ℝ)) (r : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (s : ℝ) 0) ⊆
      interior D.target.carrier := by
  obtain ⟨tN, kN, mN, hkm, hk, hm, hle, hR⟩ := hN
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  set a : ℕ := s - r with ha
  have ha1 : 1 ≤ a := by omega
  have haR : ((a : ℕ) : ℝ) + (r : ℝ) = (s : ℝ) := by
    rw [ha, Nat.cast_sub hrs.le]; ring
  have hη0 : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  obtain ⟨hπ, ⟨θ, hθ, hext⟩, ⟨iw, ie, δe, hδe, hiw, hie⟩⟩ := tN_facts C (m0 := a) hr hkm hk hm hle hR
  set x' : ℝ := x + ε * (a : ℝ) * ((u : ℝ) * v) with hx'
  have C' : CtxBaseT D u v α β γ L ax ay ε x' := ⟨C.S, C.hε⟩
  have hsh : ∀ ξ η : ℝ, lpT (u : ℝ) (v : ℝ) ε x' ξ η = lpT (u : ℝ) (v : ℝ) ε x (ξ + (a : ℝ)) η := by
    intro ξ η
    rw [hx', lpT_shift (u : ℝ) (v : ℝ) ε x (a : ℝ) (ξ + (a : ℝ)) η]
    exact lpT_congr (by ring) rfl
  have hlv : lvT (u : ℝ) (v : ℝ) ε x' (r : ℝ) = lvT (u : ℝ) (v : ℝ) ε x (s : ℝ) := by
    rw [hx', lvT_shift hε, haR]
  -- unprimed points
  have hRq : lpT (u : ℝ) (v : ℝ) ε x' 0 (r : ℝ) = lpT (u : ℝ) (v : ℝ) ε x ((a : ℝ)) (r : ℝ) := by
    rw [hsh]; exact lpT_congr (by ring) rfl
  have hQq : lpT (u : ℝ) (v : ℝ) ε x' (r : ℝ) 0 = lpT (u : ℝ) (v : ℝ) ε x (s : ℝ) 0 := by
    rw [hsh]; exact lpT_congr (by rw [← haR]; ring) rfl
  -- near towers
  have hnear' : ∀ i : ℕ, i < r → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x' (i : ℝ) (ηw r i))
      (lpT (u : ℝ) (v : ℝ) ε x' ((i : ℝ) + 1) (ηw r i)) (lpT (u : ℝ) (v : ℝ) ε x' (i : ℝ) (ηw r i + 1)) := by
    intro i hi
    obtain ⟨t, ht⟩ := Tt.1 (i + a) (r - 1 - i) (by omega) (by omega)
    have hj : ((r - 1 - i : ℕ) : ℝ) = ηw r i := by
      unfold ηw; rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
    have hi' : ((i + a : ℕ) : ℝ) = (i : ℝ) + a := by push_cast; ring
    refine ⟨t, hasV_congr ht ?_ ?_ ?_⟩
    · rw [hsh, hi', hj]
    · rw [hsh, hi', hj]; exact lpT_congr (by ring) rfl
    · rw [hsh, hi', hj]
  -- memberships in the target
  have hRmem : lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ) ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := Tt.2 (a - 1) (r - 1) (by omega) (by omega)
    have := ht.mem₃
    have e1 : ((a - 1 : ℕ) : ℝ) + 1 = (a : ℝ) := by rw [Nat.cast_sub ha1]; simp
    have e2 : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by rw [Nat.cast_sub hr]; simp
    rwa [e1, e2] at this
  have hqmem : lpT (u : ℝ) (v : ℝ) ε x (s : ℝ) 0 ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := Tt.1 (s - 1) 0 (by omega) (by omega)
    have := ht.mem₂
    have e1 : ((s - 1 : ℕ) : ℝ) + 1 = (s : ℝ) := by rw [Nat.cast_sub (by omega)]; simp
    rw [Nat.cast_zero] at this
    rwa [e1] at this
  have hq1mem : lpT (u : ℝ) (v : ℝ) ε x ((s : ℝ) - 1) 0 ∈ D.target.carrier := by
    obtain ⟨t, ht⟩ := Tt.1 (s - 1) 0 (by omega) (by omega)
    have := ht.mem₁
    have e1 : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
    simpa [e1] using this
  have hEmem : lpT (u : ℝ) (v : ℝ) ε x ((a : ℝ) + δe) (r : ℝ) ∈ D.target.carrier := by
    rw [← hie]; exact pts_mem_target D.toDissection tN ie
  have hint' : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x' 0 (r : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x' (r : ℝ) 0) ⊆
      interior D.target.carrier := by
    rw [hRq, hQq]
    exact C.seg_intT hRmem hqmem (Or.inl hη0) (Or.inl ⟨δe, hδe, hEmem⟩)
      (Or.inr ⟨1, one_pos, hq1mem⟩)
  -- the extension points
  have hθr : (0 : ℝ) < (r : ℝ) + θ := by linarith
  set P'e := lpT (u : ℝ) (v : ℝ) ε x ((a : ℝ) - θ) ((r : ℝ) + θ) with hP'e
  set Q'e := lpT (u : ℝ) (v : ℝ) ε x ((s : ℝ) + 1) (-1) with hQ'e
  have hfP' : GST (u : ℝ) (v : ℝ) ε P'e = -lvT (u : ℝ) (v : ℝ) ε x' (r : ℝ) := by
    rw [hP'e, GST_lp hε, hlv, show ((a : ℝ) - θ) + ((r : ℝ) + θ) = (s : ℝ) by rw [← haR]; ring]
  have hfQ' : GST (u : ℝ) (v : ℝ) ε Q'e = -lvT (u : ℝ) (v : ℝ) ε x' (r : ℝ) := by
    rw [hQ'e, GST_lp hε, hlv, show ((s : ℝ) + 1) + (-1) = (s : ℝ) by ring]
  have hP'm : lpT (u : ℝ) (v : ℝ) ε x' 0 (r : ℝ) ∈ openSegment ℝ P'e (lpT (u : ℝ) (v : ℝ) ε x' (r : ℝ) 0) := by
    rw [hRq, hQq, openSegment_eq_image_lineMap]
    refine ⟨θ / ((r : ℝ) + θ), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one hθr]; linarith
    · rw [hP'e, lineMap_lpT]
      refine lpT_congr ?_ ?_
      · rw [← haR]; field_simp; ring
      · field_simp; ring
  have hQ'm : lpT (u : ℝ) (v : ℝ) ε x' (r : ℝ) 0 ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x' 0 (r : ℝ)) Q'e := by
    rw [hRq, hQq, openSegment_eq_image_lineMap]
    have hr1 : (0 : ℝ) < (r : ℝ) + 1 := by linarith
    refine ⟨(r : ℝ) / ((r : ℝ) + 1), ⟨by positivity, ?_⟩, ?_⟩
    · rw [div_lt_one hr1]; linarith
    · rw [hQ'e, lineMap_lpT]
      refine lpT_congr ?_ ?_
      · rw [← haR]; field_simp; ring
      · field_simp; ring
  have hclP : ∀ e ∈ D.toDissection.lineChain (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x' (r : ℝ)),
      ¬ Straddles ((D.tile e.1).edge e.2) P'e (lpT (u : ℝ) (v : ℝ) ε x' 0 (r : ℝ))
        (lpT (u : ℝ) (v : ℝ) ε x' (r : ℝ) 0) := by
    intro e _
    rw [hRq]
    exact not_straddles_of_interior D.toDissection (j := tN) (fun y hy => hext y hy) e.1 e.2
  have hclQ : ∀ e ∈ D.toDissection.lineChain (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x' (r : ℝ)),
      ¬ Straddles ((D.tile e.1).edge e.2) Q'e (lpT (u : ℝ) (v : ℝ) ε x' (r : ℝ) 0)
        (lpT (u : ℝ) (v : ℝ) ε x' 0 (r : ℝ)) := by
    intro e _
    have hout : ∀ y ∈ openSegment ℝ Q'e (lpT (u : ℝ) (v : ℝ) ε x' (r : ℝ) 0), y ∉ D.target.carrier := by
      intro y hy hmem
      rw [hQq, hQ'e, openSegment_eq_image_lineMap] at hy
      obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
      rw [lineMap_lpT] at hmem
      have := (S.mem hmem).1
      rw [lpT_snd] at this
      have hh := S.hhpos
      have : (-1 + τ * (0 - -1)) * hhT (u : ℝ) (v : ℝ) < 0 := by nlinarith
      linarith [(S.mem hmem).1, lpT_snd (u := (u : ℝ)) (v := (v : ℝ)) ε x ((s : ℝ) + 1 + τ * ((s : ℝ) - ((s : ℝ) + 1))) (-1 + τ * (0 - -1))]
    exact not_straddles_of_outside D.toDissection hout e.1 e.2
  -- the three tiles around `R` and the base angle `β`
  obtain ⟨tV, htV⟩ := Tt.2 (a - 1) (r - 1) (by omega) (by omega)
  obtain ⟨tU, htU⟩ := Tt.1 a (r - 1) (by omega) (by omega)
  have e1 : ((a - 1 : ℕ) : ℝ) = (a : ℝ) - 1 := by rw [Nat.cast_sub ha1]; simp
  have e2 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by rw [Nat.cast_sub hr]; simp
  have htV' : HasV D tV (lpT (u : ℝ) (v : ℝ) ε x (((a - 1 : ℕ) : ℝ) + 1) ((r - 1 : ℕ) : ℝ))
      (lpT (u : ℝ) (v : ℝ) ε x ((a - 1 : ℕ) : ℝ) (((r - 1 : ℕ) : ℝ) + 1))
      (lpT (u : ℝ) (v : ℝ) ε x (((a - 1 : ℕ) : ℝ) + 1) (((r - 1 : ℕ) : ℝ) + 1)) := htV
  have aV : (D.tile tV).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) = α := by
    have := (D_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM htV').2.2
    rwa [show lpT (u : ℝ) (v : ℝ) ε x (((a - 1 : ℕ) : ℝ) + 1) (((r - 1 : ℕ) : ℝ) + 1)
      = lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ) from lpT_congr (by rw [e1]; ring) (by rw [e2]; ring)] at this
  have aU : (D.tile tU).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) = γ := by
    have := (U_anglesT hu huv hv2 hε S.tile.hab S.tile.ac S.tile.bc S.hM htU).2.2
    rwa [show lpT (u : ℝ) (v : ℝ) ε x ((a : ℕ) : ℝ) (((r - 1 : ℕ) : ℝ) + 1) = lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)
      from lpT_congr rfl (by rw [e2]; ring)] at this
  have h3α : 3 * α < Real.pi := by
    have hβpos : 0 < β := by
      have h := Erdos634.MarchFlank.cornerAngle_pos D.model 1
      have e' : cornerAngle (D.model.pts (1 + 1)) (D.model.pts 1) (D.model.pts (1 + 2)) = β := S.hM.hβ'
      rw [e'] at h; exact h
    have := S.hβ; linarith
  have hπα : (D.tile tN).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) ≠
      (D.tile tV).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) := by
    rw [hπ, aV]; intro h; have := S.hα; linarith [Real.pi_pos]
  have hπγ : (D.tile tN).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) ≠
      (D.tile tU).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) := by
    rw [hπ, aU, S.hγ]; intro h; have := S.hα; linarith [Real.pi_pos]
  have hαγ : (D.tile tV).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) ≠
      (D.tile tU).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) := by
    rw [aV, aU, S.hγ]; intro h; have := S.hα; linarith
  have n1 : tN ≠ tV := ne_of_angle hπα
  have n2 : tN ≠ tU := ne_of_angle hπγ
  have n3 : tV ≠ tU := ne_of_angle hαγ
  have hsum3 : ∑ i ∈ ({tN, tV, tU} : Finset (Fin N)), (D.tile i).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ))
      = 2 * Real.pi - β := by
    rw [Finset.sum_insert (by simp [n1, n2]), Finset.sum_insert (by simp [n3]), Finset.sum_singleton, hπ, aV, aU,
      S.hβ, S.hγ]
    ring
  have hRint : lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ) ∈ interior D.target.carrier := by
    apply Erdos634.Draft.E60Second.interior_of_sum_gt_pi D.toDissection
    have hle3 : ∑ i ∈ ({tN, tV, tU} : Finset (Fin N)), (D.tile i).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ))
        ≤ ∑ i, (D.tile i).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _ => (D.tile i).localAngle_nonneg _)
    have hβ0 : β = Real.pi - 3 * α := S.hβ
    rw [hsum3] at hle3
    linarith [S.hα]
  have htot := Erdos634.PinPlumbing.pin_angle_sum_interior D.toDissection hRint
  have hbase : 0 < r → ∀ (t : Fin N) (k m : Fin 3), k ≠ m →
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x' (((0 : ℕ) : ℝ) + 1) (ηw r 0) →
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x' ((0 : ℕ) : ℝ) (ηw r 0 + 1) →
      (∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x' (r : ℝ)) →
      (D.tile t).localAngle (lpT (u : ℝ) (v : ℝ) ε x' ((0 : ℕ) : ℝ) (ηw r 0 + 1)) = β := by
    intro _ t k m hkm' hk' hm' hle'
    rw [hlv] at hle'
    have hRe : lpT (u : ℝ) (v : ℝ) ε x' ((0 : ℕ) : ℝ) (ηw r 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ) := by
      rw [hsh]; exact lpT_congr (by simp) (by unfold ηw; simp)
    rw [hRe] at hm' ⊢
    -- `t` is none of the three tiles (it lies east of the diagonal)
    have west : ∀ {t' : Fin N} {i : Fin 3}, -lvT (u : ℝ) (v : ℝ) ε x (s : ℝ) < GST (u : ℝ) (v : ℝ) ε ((D.tile t').pts i) →
        t ≠ t' := fun {t'} {i} h => ne_of_F (D := D) (GST (u : ℝ) (v : ℝ) ε) hle' h
    have nN : t ≠ tN := west (i := iw) (by rw [← haR]; exact hiw)
    have nV : t ≠ tV := by
      obtain ⟨k2, m2, j2, -, -, -, -, hm2, -⟩ := htV
      refine west (i := m2) ?_
      rw [hm2, GST_lp hε]
      refine neg_lt_neg (lvT_lt hu huv hv2 ?_)
      rw [e1, e2, ← haR]; push_cast; linarith [(Nat.cast_nonneg (α := ℝ) 1)]
    have nU : t ≠ tU := by
      obtain ⟨k2, m2, j2, -, -, -, hk2, -, -⟩ := htU
      refine west (i := k2) ?_
      rw [hk2, GST_lp hε]
      refine neg_lt_neg (lvT_lt hu huv hv2 ?_)
      rw [e2, ← haR]; linarith
    have hnz : (D.tile t).localAngle (lpT (u : ℝ) (v : ℝ) ε x (a : ℝ) (r : ℝ)) ≠ 0 := by
      rw [← hm']; exact vertex_angle_ne_zero S t m
    exact (residue_beta_total D.toDissection D.model (fun i => (D.tiles_congruent i).symm) α S.hirr
      (S.hM.hα') (S.hM.hβ'.trans S.hβ) (S.hM.hγ'.trans S.hγ) S.hα h3α htot {tN, tV, tU}
      (hsum3.trans (by rw [S.hβ])) t (by simp [nN, nV, nU]) hnz).trans S.hβ.symm
  have key := col_orient' C' r (by omega) (by omega) hnear' hint' (P' := P'e) (Q' := Q'e) hfP' hfQ' hP'm hQ'm
    hclP hclQ hbase
  refine ⟨?_, by rw [hRq, hQq] at hint'; exact hint'⟩
  intro j hj
  obtain ⟨t, ht⟩ := key (r - 1 - j) (by omega)
  have hi : ((r - 1 - j : ℕ) : ℝ) = (r : ℝ) - 1 - j := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  have hηw : ηw r (r - 1 - j) = (j : ℝ) := by unfold ηw; rw [hi]; ring
  have hsj : ((s - 1 - j : ℕ) : ℝ) = (s : ℝ) - 1 - j := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]; simp
  refine ⟨t, hasV_congr ht ?_ ?_ ?_⟩
  · rw [hsh, hηw]; exact lpT_congr (by rw [hi, hsj, ← haR]; ring) rfl
  · rw [hsh, hηw]; exact lpT_congr (by rw [hi, hsj, ← haR]; ring) rfl
  · rw [hsh, hηw]; exact lpT_congr (by rw [hi, hsj, ← haR]; ring) rfl

#print axioms L32_B
end Erdos634.Draft.ThmDRun
