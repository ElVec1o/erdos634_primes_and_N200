/-
Draft/S1Inst.lean -- the S1 leaf `S1Closed N` (base-β isosceles target `(β, β, 3α)`) from its scaled instances.

`NSQS1.s1Closed_of_free` proves `S1Closed N` when no `t ≥ 2`, coprime `p < q` have `N = t²(3q² − p²)` (`S1Free N`).
Here each such triple is carried as a leaf `S1Inst t p q`: "no dissection of the isosceles triangle with legs `t q³` and
base `t p (3q² − p²)` (the base-β target `Δ₁(p,q)` scaled by `t`) by the tile `(p q, q² − p², q²)`".  The proof is
`CompositeFinal4.s1_baseBetaTiled_of_arith` verbatim, except that the step `M = p + q` comes from `NSQS1.s1_arith_t`
(`M = t (p+q)`): `t = 1` gives it, `t ≥ 2` is refuted by the instance after scaling by `q²/c`.
`s1inst_of_cert` discharges an instance from a search certificate by SSS.

Composite-N leaves (this is the base-β `m ≥ 2` family, one member at a time); not prime-case work.
No sorry, no native_decide.
-/
import Erdos634.Draft.NSQS1
import Erdos634.Draft.GapE120Dis

set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 400000

namespace Erdos634.Draft.CompositeFinal4

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Realizable Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeS1Arith

/-- **The S1 instance `(t, p, q)`**: no dissection (any number of tiles) of the isosceles triangle with legs `t q³` and
base `t p (3q² − p²)` by the tile with sides `(p q, q² − p², q²)`. -/
def S1Inst (t p q : ℤ) : Prop :=
  ∀ {N : ℕ} (D : CongruentDissection N),
    D.target.oppLen 0 = (t : ℝ) * (q : ℝ) ^ 3 →
    D.target.oppLen 1 = (t : ℝ) * (q : ℝ) ^ 3 →
    D.target.oppLen 2 = (t : ℝ) * p * (3 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) →
    (∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = (p : ℝ) * q ∧
      D.model.oppLen (σ 1) = (q : ℝ) ^ 2 - (p : ℝ) ^ 2 ∧ D.model.oppLen (σ 2) = (q : ℝ) ^ 2) → False

open Erdos634.Geometry.GapE120Dis in
/-- an S1 instance from a certificate whose target is labelled (leg, base, leg) in the vertex order `01, 12, 02`
and whose model has sides `(p q, q²−p², q²)` in that order -/
theorem s1inst_of_cert_lbl (t p q : ℤ) (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (t : ℝ) * (q : ℝ) ^ 3 ∧
      dist (TGT.pts 1) (TGT.pts 2) = (t : ℝ) * p * (3 * (q : ℝ) ^ 2 - (p : ℝ) ^ 2) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (t : ℝ) * (q : ℝ) ^ 3)
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (p : ℝ) * q ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (q : ℝ) ^ 2 - (p : ℝ) ^ 2 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (q : ℝ) ^ 2)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    S1Inst t p q := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  have hTc : D.target.Congruent TGT := by
    set ρ : Equiv.Perm (Fin 3) := (finRotate 3).symm with hρ
    have r0 : ρ 0 = 2 := by rw [hρ]; decide
    have r1 : ρ 1 = 0 := by rw [hρ]; decide
    have r2 : ρ 2 = 1 := by rw [hρ]; decide
    have hc := Tri.congruent_of_dist (D.target.relabel ρ) TGT
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r0, r1, g1, ← h1]; rfl)
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r1, r2, g2, ← h2]; rfl)
      (by simp only [Tri.relabel_pts, Function.comp]; rw [r0, r2, g3, ← h0, dist_comm]; rfl)
    exact (D.target.congruent_relabel ρ).trans hc
  obtain ⟨s1, s2, s3⟩ := sides_of_perm D.model σ
  rw [m0] at s1; rw [m1] at s2; rw [m2] at s3
  have hMc : D.model.Congruent MODEL := by
    set τ : Equiv.Perm (Fin 3) := (finRotate 3).trans σ with hτ
    have h0' : τ 0 = σ 1 := by simp [hτ, fr0]
    have h1' : τ 1 = σ 2 := by simp [hτ, fr1]
    have h2' : τ 2 = σ 0 := by simp [hτ, fr2]
    have hc := Tri.congruent_of_dist (D.model.relabel τ) MODEL
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h1', s1, k1])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h1', h2', dist_comm, s2, k2])
      (by simp only [Tri.relabel_pts, Function.comp]; rw [h0', h2', dist_comm, s3, k3])
    exact (D.model.congruent_relabel τ).trans hc
  exact hno D hTc hMc

open Erdos634.Draft.ScaleBaseBetaFull in
set_option maxHeartbeats 4000000 in
theorem s1_baseBetaTiled_of_inst (N : ℕ)
    (hinst : ∀ t p q : ℤ, 2 ≤ t → 0 < p → p < q → IsCoprime p q → (N : ℤ) = t ^ 2 * (3 * q ^ 2 - p ^ 2) →
      S1Inst t p q)
    (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ) (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi)
    (hmod : D.model.ThreeAlphaData α β a b c) (har : a = (r : ℝ) * c)
    (hbr : b = (1 - (r : ℝ) ^ 2) * c) (htgt : TgtAngles D β β (3 * α)) : BaseBetaTiled := by
  -- Step 0: relabel target so β at positions 0, 1
  obtain ⟨σ_t, ht0, ht1, _⟩ := htgt
  set D' := D.relabelTarget' σ_t
  have hD'_tgt_pts : ∀ k, D'.target.pts k = D.target.pts (σ_t k) := fun _ => rfl
  have hD'_tgt0 : D'.target.angleAt 0 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 0).trans ht0
  have hD'_tgt1 : D'.target.angleAt 1 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 1).trans ht1
  -- Step 1: Row12.setup (D'.model = D.model definitionally)
  obtain ⟨s, M, hs0, hs1, hc, ha_sc, hb_sc, hM2, _, hM0, _, hMleg, hYs, hquad⟩ :=
    Row12.setup D' hα hrel hmod hD'_tgt0 hD'_tgt1
  -- Step 2: s = r
  have hsr : s = (r : ℝ) := mul_right_cancel₀ hc.ne' (by rw [← ha_sc, ← har])
  -- p = r.num, q = r.den (as integers)
  set p_i := r.num
  set q_i : ℤ := (r.den : ℤ)
  have hq_pos : (0 : ℤ) < q_i := by
    show (0 : ℤ) < (r.den : ℤ); exact_mod_cast r.pos
  have hcop_pq : IsCoprime p_i q_i := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast r.reduced
  have hq_r : (q_i : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hr_pq : (r : ℝ) = (p_i : ℝ) / (q_i : ℝ) := by
    have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
    simpa [p_i, q_i, Int.cast_natCast] using h1
  have hp_pos : (0 : ℤ) < p_i := by
    have hpR : (0 : ℝ) < (p_i : ℝ) := by
      have := hs0; rw [hsr, hr_pq] at this
      have hqR : (0 : ℝ) < (q_i : ℝ) := by exact_mod_cast hq_pos
      rcases div_pos_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · linarith
    exact_mod_cast hpR
  have hp_lt_q : p_i < q_i := by
    have := hs1; rw [hsr, hr_pq] at this
    exact_mod_cast (div_lt_one (by exact_mod_cast hq_pos)).mp this
  -- Step 3: quadratic as integers
  have hquad_int : (N : ℤ) * (p_i + q_i) ^ 2 = M ^ 2 * (3 * q_i ^ 2 - p_i ^ 2) := by
    have hkey := hquad; rw [hsr, hr_pq] at hkey
    have hkey2 : (q_i : ℝ) ^ 2 * (((N : ℝ) + (M : ℝ) ^ 2) * ((p_i : ℝ) / q_i) ^ 2 +
        2 * N * ((p_i : ℝ) / q_i) + ((N : ℝ) - 3 * (M : ℝ) ^ 2)) = 0 := by
      rw [hkey]; ring
    have hkey3 : (N : ℝ) * (p_i + q_i) ^ 2 = (M : ℝ) ^ 2 * (3 * q_i ^ 2 - p_i ^ 2) := by
      have hq2 : (q_i : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_r
      field_simp at hkey2 ⊢
      nlinarith [hkey2, sq_nonneg (p_i : ℝ), sq_nonneg (q_i : ℝ)]
    exact_mod_cast hkey3
  have hB_pos : (0 : ℤ) < 3 * q_i ^ 2 - p_i ^ 2 := by nlinarith [sq_nonneg p_i, sq_nonneg q_i]
  have hpq_pos : (0 : ℤ) < p_i + q_i := by linarith [hp_pos, hq_pos]
  have hMeq : M = p_i + q_i := by
    obtain ⟨t, ht0, hMt, hNt⟩ := Erdos634.Draft.NSQS1.s1_arith_t hp_pos hp_lt_q hcop_pq hM0 hquad_int
    by_cases ht1 : t = 1
    · rw [hMt, ht1]; ring
    · exfalso
      have ht2 : 2 ≤ t := by omega
      have hqR : (0 : ℝ) < (q_i : ℝ) := by exact_mod_cast hq_pos
      have hpqR : (0 : ℝ) < (q_i : ℝ) + p_i := by exact_mod_cast (by linarith : (0 : ℤ) < q_i + p_i)
      have hMR : (M : ℝ) = (t : ℝ) * ((p_i : ℝ) + q_i) := by exact_mod_cast hMt
      -- legs
      have hX : D'.target.oppLen 0 = (t : ℝ) * c * q_i := by
        have h1 := hMleg; rw [hMR, hsr, hr_pq] at h1
        have h2 : D'.target.oppLen 0 * (1 + (p_i : ℝ) / q_i) * q_i = D'.target.oppLen 0 * ((q_i : ℝ) + p_i) := by
          field_simp
        have h3 : D'.target.oppLen 0 * ((q_i : ℝ) + p_i) = ((t : ℝ) * c * q_i) * ((q_i : ℝ) + p_i) := by
          rw [← h2, ← h1]; ring
        exact mul_right_cancel₀ hpqR.ne' h3
      have hX1g : D'.target.oppLen 1 = D'.target.oppLen 0 := by
        have hlaw := Tri.lawSin D'.target 0 1
        rw [hD'_tgt0, hD'_tgt1] at hlaw
        have hβ_pos : 0 < β := by
          have := Tri.angleAt_pos' D'.target 0; rwa [hD'_tgt0] at this
        have hβ_lt_pi : β < Real.pi := by
          have hsum := D'.target.angleAt_sum; rw [hD'_tgt0, hD'_tgt1] at hsum
          linarith [Tri.angleAt_pos' D'.target 2]
        have hs_pos : 0 < Real.sin β := Real.sin_pos_of_pos_of_lt_pi hβ_pos hβ_lt_pi
        exact mul_left_cancel₀ hs_pos.ne' hlaw
      obtain ⟨σm, _, ham, _, hbm, _, hcm⟩ := hmod
      set sc : ℝ := (q_i : ℝ) ^ 2 / c with hsc
      have hscpos : 0 < sc := div_pos (by positivity) hc
      set Ds := scaleDissection (D'.model.pts 0) sc hscpos.ne' D' with hDs
      have htd : ∀ i j : Fin 3, dist (Ds.target.pts i) (Ds.target.pts j) = sc * dist (D'.target.pts i) (D'.target.pts j) := by
        intro i j
        rw [hDs, scaleDissection_target_pts, scaleDissection_target_pts, homothetyEquiv_dist, abs_of_pos hscpos]
      have hmd : ∀ i j : Fin 3, dist (Ds.model.pts i) (Ds.model.pts j) = sc * dist (D'.model.pts i) (D'.model.pts j) := by
        intro i j
        rw [hDs, scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist, abs_of_pos hscpos]
      have hto : ∀ k : Fin 3, Ds.target.oppLen k = sc * D'.target.oppLen k := fun k => by
        unfold Tri.oppLen; exact htd _ _
      have hmo : ∀ k : Fin 3, Ds.model.oppLen k = sc * D.model.oppLen k := fun k => by
        unfold Tri.oppLen; exact hmd _ _
      refine hinst t p_i q_i ht2 hp_pos hp_lt_q hcop_pq hNt Ds ?_ ?_ ?_ ⟨σm, ?_, ?_, ?_⟩
      · rw [hto, hX, hsc]; first | (field_simp; ring) | field_simp
      · rw [hto, hX1g, hX, hsc]; first | (field_simp; ring) | field_simp
      · rw [hto, hYs, hX, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
      · rw [hmo, ham, ha_sc, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
      · rw [hmo, hbm, hb_sc, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
      · rw [hmo, hcm, hsc]; first | (field_simp; ring) | field_simp
  -- Step 5: e = p, f = q (natural numbers)
  set e_n : ℕ := p_i.natAbs
  set f_n : ℕ := q_i.natAbs
  have he_pos : 0 < e_n := Int.natAbs_pos.mpr (Int.ne_of_gt hp_pos)
  have he_int : (e_n : ℤ) = p_i := Int.natAbs_of_nonneg hp_pos.le
  have hf_int : (f_n : ℤ) = q_i := Int.natAbs_of_nonneg hq_pos.le
  have hef_lt : e_n < f_n := by
    have : (e_n : ℤ) < (f_n : ℤ) := by rw [he_int, hf_int]; exact hp_lt_q
    exact_mod_cast this
  have hcop_nat : Nat.Coprime e_n f_n := by
    show Nat.Coprime p_i.natAbs q_i.natAbs
    rw [Nat.Coprime]; exact_mod_cast r.reduced
  have he_cast : (e_n : ℝ) = (p_i : ℝ) := by exact_mod_cast he_int
  have hf_cast : (f_n : ℝ) = (q_i : ℝ) := by exact_mod_cast hf_int
  -- Step 6: scale and relabel model
  -- D'.model = D.model definitionally (relabelTarget' only changes target)
  have hmod' : D'.model.ThreeAlphaData α β a b c := hmod
  obtain ⟨σ_mdl, _, ho_a0, _, ho_b1, _, ho_c2⟩ := hmod'
  set scale_r := (f_n : ℝ) ^ 2 / c
  have hscale_pos : 0 < scale_r := div_pos (by positivity) hc
  let D_sc := scaleDissection (D'.model.pts 0) scale_r hscale_pos.ne' D'
  let D'' := D_sc.relabelModel σ_mdl
  have hoppLen : ∀ k : Fin 3, D''.model.oppLen k =
      scale_r * D'.model.oppLen (σ_mdl k) := fun k => by
    have heq : D''.model.oppLen k = D_sc.model.oppLen (σ_mdl k) :=
      Row14AnyLabel.oppLen_of_pts σ_mdl (fun _ => rfl) k
    rw [heq]
    unfold Tri.oppLen
    rw [scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist,
        abs_of_nonneg (le_of_lt hscale_pos)]
  have hso : ∀ (T : Erdos634.Geometry.Tri) (k : Fin 3), sideOpp T k = T.oppLen k := fun _ _ => rfl
  have hm0 : sideOpp D''.model 0 = (e_n : ℝ) * f_n := by
    rw [hso, hoppLen 0, ho_a0, ha_sc,
        show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hsr, hr_pq, hf_cast, he_cast]
    field_simp
  have hm1 : sideOpp D''.model 1 = (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2 := by
    rw [hso, hoppLen 1, ho_b1, hb_sc,
        show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hsr, hr_pq, hf_cast, he_cast]
    field_simp
  have hm2 : sideOpp D''.model 2 = (f_n : ℝ) ^ 2 := by
    rw [hso, hoppLen 2, ho_c2, show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hf_cast]
    field_simp
  -- Step 7: target congruence
  -- D''.target = D_sc.target (relabelModel does not change target)
  have hD''_tpts : ∀ k, D''.target.pts k =
      homothetyEquiv (D'.model.pts 0) scale_r hscale_pos.ne' (D'.target.pts k) :=
    fun _ => rfl
  set X := D'.target.oppLen 0
  have hX1 : D'.target.oppLen 1 = X := by
    have hlaw := Tri.lawSin D'.target 0 1
    rw [hD'_tgt0, hD'_tgt1] at hlaw
    have hβ_pos : 0 < β := by
      have := Tri.angleAt_pos' D'.target 0; rwa [hD'_tgt0] at this
    have hβ_lt_pi : β < Real.pi := by
      have hsum := D'.target.angleAt_sum; rw [hD'_tgt0, hD'_tgt1] at hsum
      linarith [Tri.angleAt_pos' D'.target 2]
    have hs_pos : 0 < Real.sin β :=
      Real.sin_pos_of_pos_of_lt_pi hβ_pos hβ_lt_pi
    exact mul_left_cancel₀ hs_pos.ne' hlaw
  have hX_cq : X = c * (q_i : ℝ) := by
    have hMeq_r : (M : ℝ) = (p_i : ℝ) + q_i := by exact_mod_cast hMeq
    have hpq_ne : (p_i : ℝ) + (q_i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hpq_pos)
    have h1 : ((p_i : ℝ) + q_i) * c = X * (1 + (p_i : ℝ) / q_i) := by
      have := hMleg; rw [hMeq_r, hsr, hr_pq] at this; exact this
    have h2 : ((p_i : ℝ) + q_i) * (X - c * q_i) = 0 := by
      field_simp at h1; linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hpq_ne
    · linarith
  have hX_eq : scale_r * X = (f_n : ℝ) ^ 3 := by
    rw [show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hX_cq, hf_cast]
    field_simp
  have hhe : (0 : ℝ) < (e_n : ℝ) := by exact_mod_cast he_pos
  have hhef : (e_n : ℝ) < (f_n : ℝ) := by exact_mod_cast hef_lt
  have hbaseLen : baseLen (e_n : ℝ) f_n = (e_n : ℝ) * (3 * (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    unfold baseLen Nq; ring
  -- Distances in D''.target (scaled by scale_r from D'.target)
  -- oppLen 2 T = dist (T.pts 0) (T.pts 1), oppLen 0 T = dist (T.pts 1) (T.pts 2),
  -- oppLen 1 T = dist (T.pts 2) (T.pts 0) — all rfl in Fin 3
  have hd01 : dist (D''.target.pts 0) (D''.target.pts 1) = baseLen (e_n : ℝ) f_n := by
    rw [hD''_tpts 0, hD''_tpts 1, homothetyEquiv_dist, abs_of_pos hscale_pos,
        show dist (D'.target.pts 0) (D'.target.pts 1) = D'.target.oppLen 2 from rfl]
    rw [hYs, hX_cq, show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hsr, hr_pq, he_cast, hf_cast]
    unfold baseLen Nq; field_simp
  have hd12 : dist (D''.target.pts 1) (D''.target.pts 2) = (f_n : ℝ) ^ 3 := by
    have : dist (D''.target.pts 1) (D''.target.pts 2) = scale_r * X := by
      rw [hD''_tpts 1, hD''_tpts 2, homothetyEquiv_dist, abs_of_pos hscale_pos,
          show dist (D'.target.pts 1) (D'.target.pts 2) = X from rfl]
    rw [this, hX_eq]
  have hd20 : dist (D''.target.pts 2) (D''.target.pts 0) = (f_n : ℝ) ^ 3 := by
    have : dist (D''.target.pts 2) (D''.target.pts 0) = scale_r * X := by
      rw [hD''_tpts 2, hD''_tpts 0, homothetyEquiv_dist, abs_of_pos hscale_pos,
          show dist (D'.target.pts 2) (D'.target.pts 0) = D'.target.oppLen 1 from rfl,
          hX1]
    rw [this, hX_eq]
  have htgt_cong : D''.target.Congruent
      (baseBetaTarget (e_n : ℝ) f_n (by exact_mod_cast he_pos) (by exact_mod_cast hef_lt)) :=
    SssCongruent.congruent_of_dist_three
      (by rw [hd01, baseBetaTarget_dist_base hhe hhef]; exact hbaseLen)
      (by rw [hd12, baseBetaTarget_dist_leg₁ hhe hhef])
      (by rw [hd20, dist_comm, baseBetaTarget_dist_leg₀ hhe hhef])
  exact ⟨e_n, f_n, he_pos, hef_lt, hcop_nat, N, D'', htgt_cong, hm0, hm1, hm2⟩

/-- **`S1Closed N` from the instances.** -/
theorem s1Closed_of_inst (N : ℕ)
    (hinst : ∀ t p q : ℤ, 2 ≤ t → 0 < p → p < q → IsCoprime p q → (N : ℤ) = t ^ 2 * (3 * q ^ 2 - p ^ 2) →
      S1Inst t p q) : Erdos634.Draft.CompositeS1Arith.S1Closed N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exact not_baseBetaTiled (s1_baseBetaTiled_of_inst N hinst D α β a b c r hα hrel hmod har hbr htgt)

end Erdos634.Draft.CompositeFinal4

#print axioms Erdos634.Draft.CompositeFinal4.s1Closed_of_inst
