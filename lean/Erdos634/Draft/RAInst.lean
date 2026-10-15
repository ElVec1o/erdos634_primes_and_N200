/-
Draft/RAInst.lean -- the S5 leaf `RAStatementNsq N` from its finitely many scaled instances.

`NSQMRA.raStatement_nsqM` proves `RAStatementNsq N` when `N` is `S5pFree` (no `t ≥ 2`, coprime `e < f` with
`N = t²(f² − e²)`).  Here each such triple `(t, e, f)` is instead carried as a leaf `S5Inst t e f`:
"no dissection of the isosceles triangle with legs `t f (f²−e²)` and base `t e (f²−e²)` by the tile `(e f, f²−e², f²)`".
The proof is `raStatement_nsqM` verbatim, with the one arithmetic step `N ∣ (f−e)K` obtained from `km_shape`
(`K = (f+e)t`, `M = (f−e)t`): `t = 1` gives the divisibility, `t ≥ 2` is refuted by the instance after scaling by `f²/c`.
`s5inst_of_cert` discharges an instance from a search certificate by SSS.

Composite-N leaves; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQMRA
import Erdos634.Draft.GapE120Dis

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RAAssemble Erdos634.CertCoord

namespace Erdos634.Draft.NSQM

/-- the shape of `(K, M)`: the first half of `s5pFree_imp_radvdM` -/
theorem km_shape {N : ℕ} {e f K M : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) (hK : 0 < K) (hM : 0 < M)
    (hNKM : (N : ℤ) = K * M) (hKp : (2 : ℤ) ∣ K - N) (hMp : (2 : ℤ) ∣ M - N) (hrel : K * (f - e) = M * (f + e)) :
    ∃ t : ℤ, 0 < t ∧ K = (f + e) * t ∧ M = (f - e) * t ∧ (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) := by
  have hfe : f * (K - M) = e * (K + M) := by linarith
  have hdvd : f ∣ K + M := hcop.symm.dvd_of_dvd_mul_left ⟨K - M, by linarith⟩
  obtain ⟨u, hu⟩ := hdvd
  have hf0 : 0 < f := by omega
  have hKM : K - M = e * u := by
    have : f * (K - M) = f * (e * u) := by rw [hfe, hu]; ring
    exact mul_left_cancel₀ hf0.ne' this
  have hupos : 0 < u := by
    by_contra hle; push Not at hle
    nlinarith
  have hKMe : Even (K + M) := by
    obtain ⟨a, ha⟩ := hKp; obtain ⟨b, hb⟩ := hMp; exact ⟨a + b + N, by linarith⟩
  have hKMe' : Even (K - M) := by
    obtain ⟨a, ha⟩ := hKp; obtain ⟨b, hb⟩ := hMp; exact ⟨a - b, by linarith⟩
  have hue : Even u := by
    by_contra hodd
    have h1 : Even (f * u) := by rw [← hu]; exact hKMe
    have h2 : Even (e * u) := by rw [← hKM]; exact hKMe'
    rw [Int.even_mul] at h1 h2
    exact not_both_even hcop (h2.resolve_right hodd) (h1.resolve_right hodd)
  obtain ⟨t, ht⟩ := hue
  have htpos : 0 < t := by omega
  have hK' : K = (f + e) * t := by rw [ht] at hu hKM; linarith
  have hM' : M = (f - e) * t := by rw [ht] at hu hKM; linarith
  exact ⟨t, htpos, hK', hM', by rw [hNKM, hK', hM']; ring⟩

/-- **The S5 instance `(t, e, f)`**: no dissection (any number of tiles) of the isosceles triangle with legs
`t f (f² − e²)` and base `t e (f² − e²)` by the tile with sides `(e f, f² − e², f²)`. -/
def S5Inst (t e f : ℤ) : Prop :=
  ∀ {N : ℕ} (D : CongruentDissection N),
    D.target.oppLen 0 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    D.target.oppLen 1 = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    D.target.oppLen 2 = (t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) →
    (∃ σ : Equiv.Perm (Fin 3), D.model.oppLen (σ 0) = (e : ℝ) * f ∧
      D.model.oppLen (σ 1) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ D.model.oppLen (σ 2) = (f : ℝ) ^ 2) → False

open Erdos634.Geometry.GapE120Dis in
/-- an S5 instance from a certificate: `TGT` has sides (base, leg, leg) and `MODEL` sides `(e f, f²−e², f²)`
in the vertex order `01, 12, 02` -/
theorem s5inst_of_cert (t e f : ℤ) (TGT MODEL : Erdos634.Geometry.Tri)
    (hT : dist (TGT.pts 0) (TGT.pts 1) = (t : ℝ) * e * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 1) (TGT.pts 2) = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ∧
      dist (TGT.pts 0) (TGT.pts 2) = (t : ℝ) * f * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2))
    (hM : dist (MODEL.pts 0) (MODEL.pts 1) = (e : ℝ) * f ∧
      dist (MODEL.pts 1) (MODEL.pts 2) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 ∧ dist (MODEL.pts 0) (MODEL.pts 2) = (f : ℝ) ^ 2)
    (hno : ∀ {N : ℕ} (D : CongruentDissection N), D.target.Congruent TGT → D.model.Congruent MODEL → False) :
    S5Inst t e f := by
  intro N D h0 h1 h2 ⟨σ, m0, m1, m2⟩
  obtain ⟨g1, g2, g3⟩ := hT
  obtain ⟨k1, k2, k3⟩ := hM
  have hTc : D.target.Congruent TGT := by
    refine Tri.congruent_of_dist _ _ ?_ ?_ ?_
    · rw [g1, ← h2]; rfl
    · rw [g2, ← h0]; rfl
    · rw [g3, ← h1, dist_comm]; rfl
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

set_option maxHeartbeats 4000000 in
theorem raStatement_of_inst (N : ℕ)
    (hinst : ∀ t e f : ℤ, 2 ≤ t → 0 < e → e < f → IsCoprime e f → (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) → S5Inst t e f) :
    Erdos634.Draft.NSQRA.RAStatementNsq N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  -- Step 0: relabel the target so its angles are (α+β, α+β, α) at vertices 0, 1, 2
  obtain ⟨σ_t, ht0, ht1, ht2⟩ := htgt
  set D' := D.relabelTarget' σ_t
  have hD'_tgt_pts : ∀ k, D'.target.pts k = D.target.pts (σ_t k) := fun _ => rfl
  have hP0 : D'.target.angleAt 0 = α + β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 0).trans ht0
  have hP1 : D'.target.angleAt 1 = α + β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 1).trans ht1
  -- Step 1: Row 13 with area
  obtain ⟨s, K, hs0, hs1, hc, ha_sc, hb_sc, hO1, hO2, hKc, hNK, M, hNKM, hKp, hMp, hMc⟩ :=
    setupM D' hα hrel hmod hP0 hP1
  have hsr : s = (r : ℝ) := mul_right_cancel₀ hc.ne' (by rw [← ha_sc, ← har])
  set p_i := r.num
  set q_i : ℤ := (r.den : ℤ)
  have hq_pos : (0 : ℤ) < q_i := by show (0 : ℤ) < (r.den : ℤ); exact_mod_cast r.pos
  have hq_r : (q_i : ℝ) ≠ 0 := by exact_mod_cast hq_pos.ne'
  have hr_pq : (r : ℝ) = (p_i : ℝ) / (q_i : ℝ) := by
    have h1 : (r : ℝ) = (r.num : ℝ) / (r.den : ℝ) := Rat.cast_def r
    simpa [p_i, q_i, Int.cast_natCast] using h1
  have hqR : (0 : ℝ) < (q_i : ℝ) := by exact_mod_cast hq_pos
  have hp_pos : (0 : ℤ) < p_i := by
    have hpR : (0 : ℝ) < (p_i : ℝ) := by
      have := hs0; rw [hsr, hr_pq] at this
      rcases div_pos_iff.mp this with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact h1
      · linarith
    exact_mod_cast hpR
  have hp_lt_q : p_i < q_i := by
    have := hs1; rw [hsr, hr_pq] at this
    exact_mod_cast (div_lt_one hqR).mp this
  have hpR : (0 : ℝ) < (p_i : ℝ) := by exact_mod_cast hp_pos
  -- Step 2: K > 0, and the integer equation
  have hX0pos : 0 < D'.target.oppLen 0 := Row3.RP.oppLen_pos D'.target 0
  have hKpos : 0 < K := by
    have h1 : (0 : ℝ) < (K : ℝ) * c * (1 - s) := by rw [hKc]; exact hX0pos
    have h2 : (0 : ℝ) < (K : ℝ) := by
      by_contra hle; push Not at hle
      have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle hc.le)
        (by linarith : (0 : ℝ) ≤ 1 - s)
      linarith
    exact_mod_cast h2
  have hEq : (N : ℤ) * (q_i + p_i) = K ^ 2 * (q_i - p_i) := by
    have h1 := hNK; rw [hsr, hr_pq] at h1
    have h2 : (N : ℝ) * ((q_i : ℝ) + p_i) = (K : ℝ) ^ 2 * ((q_i : ℝ) - p_i) := by
      field_simp at h1; linarith
    exact_mod_cast h2
  have hMpos : 0 < M := by
    have h1 : (0 : ℝ) < (M : ℝ) * c * (1 + s) := by rw [hMc]; exact hX0pos
    have h2 : (0 : ℝ) < (M : ℝ) := by
      by_contra hle; push Not at hle
      have := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hle hc.le)
        (by linarith : (0 : ℝ) ≤ 1 + s)
      linarith
    exact_mod_cast h2
  have hrelKM : K * (q_i - p_i) = M * (q_i + p_i) := by
    have h1 : (K : ℝ) * (1 - s) = (M : ℝ) * (1 + s) := by
      have : c * ((K : ℝ) * (1 - s) - (M : ℝ) * (1 + s)) = 0 := by linear_combination hKc - hMc
      have := (mul_eq_zero.mp this).resolve_left hc.ne'
      linarith
    rw [hsr, hr_pq] at h1
    have h2 : (K : ℝ) * ((q_i : ℝ) - p_i) = (M : ℝ) * ((q_i : ℝ) + p_i) := by
      field_simp at h1; linarith
    exact_mod_cast h2
  -- Step 3: k = Nσ
  have hcop_pq : IsCoprime p_i q_i := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast r.reduced
  have hdvd : (N : ℤ) ∣ (q_i - p_i) * K := by
    obtain ⟨t, ht0, hKt, hMt, hNt⟩ := km_shape hp_pos hp_lt_q hcop_pq hKpos hMpos hNKM hKp hMp hrelKM
    by_cases ht2 : 2 ≤ t
    · exfalso
      obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hmod
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
      have hKR : (K : ℝ) = ((q_i : ℝ) + p_i) * t := by exact_mod_cast hKt
      have hX0 : D'.target.oppLen 0 = (t : ℝ) * c * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / q_i := by
        rw [← hKc, hsr, hr_pq, hKR]; first | (field_simp; ring) | field_simp
      refine hinst t p_i q_i ht2 hp_pos hp_lt_q hcop_pq hNt Ds ?_ ?_ ?_ ⟨σm, ?_, ?_, ?_⟩
      · rw [hto, hX0, hsc]; first | (field_simp; ring) | field_simp
      · rw [hto, hO1, hX0, hsc]; first | (field_simp; ring) | field_simp
      · rw [hto, hO2, hX0, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
      · rw [hmo, ham, ha_sc, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
      · rw [hmo, hbm, hb_sc, hsr, hr_pq, hsc]; first | (field_simp; ring) | field_simp
      · rw [hmo, hcm, hsc]; first | (field_simp; ring) | field_simp
    · have ht1 : t = 1 := by omega
      subst ht1
      exact ⟨1, by rw [hKt, hNt]; ring⟩
  obtain ⟨σz, hσpos, hσb, hσk⟩ := ra_arith_nsqM (by have := D.pos; omega) hdvd hp_pos hp_lt_q hKpos hEq
  set σn : ℕ := σz.toNat
  have hσn : (σn : ℤ) = σz := Int.toNat_of_nonneg hσpos.le
  have hσn_pos : 0 < σn := by omega
  have hσR : (σn : ℝ) = (σz : ℝ) := by exact_mod_cast hσn
  have hσb_R : (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2 = (N : ℝ) * (σz : ℝ) ^ 2 := by exact_mod_cast hσb
  have hσk_R : ((q_i : ℝ) - p_i) * (K : ℝ) = (N : ℝ) * (σz : ℝ) := by exact_mod_cast hσk
  -- Step 4: the target's sides
  have hO0 : D'.target.oppLen 0 = (N : ℝ) * (σz : ℝ) * c / (q_i : ℝ) := by
    rw [← hKc, hsr, hr_pq]
    have : (K : ℝ) * c * (1 - (p_i : ℝ) / q_i) = ((q_i : ℝ) - p_i) * (K : ℝ) * c / q_i := by
      field_simp
    rw [this, hσk_R]
  have hO1' : D'.target.oppLen 1 = (N : ℝ) * (σz : ℝ) * c / (q_i : ℝ) := by rw [hO1, hO0]
  have hO2' : D'.target.oppLen 2 = (p_i : ℝ) * (N : ℝ) * (σz : ℝ) * c / (q_i : ℝ) ^ 2 := by
    rw [hO2, hO0, hsr, hr_pq]; field_simp
  -- Step 5: natural-number parameters
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
  -- Step 6: scale by f²/c, relabel the model
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hmod
  set scale_r := (f_n : ℝ) ^ 2 / c with hscale
  have hscale_pos : 0 < scale_r := div_pos (by positivity) hc
  let D_sc := scaleDissection (D'.model.pts 0) scale_r hscale_pos.ne' D'
  let D'' := D_sc.relabelModel σm
  have hoppLen : ∀ k : Fin 3, D''.model.oppLen k = scale_r * D'.model.oppLen (σm k) := fun k => by
    have heq : D''.model.oppLen k = D_sc.model.oppLen (σm k) :=
      Row14AnyLabel.oppLen_of_pts σm (fun _ => rfl) k
    rw [heq]
    unfold Tri.oppLen
    rw [scaleDissection_model_pts, scaleDissection_model_pts, homothetyEquiv_dist,
      abs_of_nonneg (le_of_lt hscale_pos)]
  have hso : ∀ (T : Erdos634.Geometry.Tri) (k : Fin 3), sideOpp T k = T.oppLen k := fun _ _ => rfl
  have hm0 : sideOpp D''.model 0 = (e_n : ℝ) * f_n := by
    rw [hso, hoppLen 0]
    show scale_r * D.model.oppLen (σm 0) = _
    rw [ham, ha_sc, hscale, hsr, hr_pq, hf_cast, he_cast]; field_simp
  have hm1 : sideOpp D''.model 1 = (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2 := by
    rw [hso, hoppLen 1]
    show scale_r * D.model.oppLen (σm 1) = _
    rw [hbm, hb_sc, hscale, hsr, hr_pq, hf_cast, he_cast]; field_simp
  have hm2 : sideOpp D''.model 2 = (f_n : ℝ) ^ 2 := by
    rw [hso, hoppLen 2]
    show scale_r * D.model.oppLen (σm 2) = _
    rw [hcm, hscale, hf_cast]; field_simp
  -- Step 7: rotate the target so the apex is vertex 0, then the ladder distances
  let D3 := D''.relabelTarget' (finRotate 3).symm
  have hD''_tpts : ∀ k, D''.target.pts k =
      homothetyEquiv (D'.model.pts 0) scale_r hscale_pos.ne' (D'.target.pts k) := fun _ => rfl
  have hD3p0 : D3.target.pts 0 = D''.target.pts 2 := rfl
  have hD3p1 : D3.target.pts 1 = D''.target.pts 0 := rfl
  have hD3p2 : D3.target.pts 2 = D''.target.pts 1 := rfl
  have hdist : ∀ i j : Fin 3, dist (D''.target.pts i) (D''.target.pts j) = scale_r * dist (D'.target.pts i) (D'.target.pts j) := by
    intro i j
    rw [hD''_tpts i, hD''_tpts j, homothetyEquiv_dist, abs_of_pos hscale_pos]
  have hσf : (σn : ℝ) * dist (D3.target.pts 0) (D3.target.pts 1)
      = (f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD3p0, hD3p1, hdist, show dist (D'.target.pts 2) (D'.target.pts 0) = D'.target.oppLen 1 from rfl,
      hO1', hscale, hσR, hf_cast, he_cast, hσb_R]
    field_simp
  have hσe : (σn : ℝ) * dist (D3.target.pts 1) (D3.target.pts 2)
      = (e_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD3p1, hD3p2, hdist, show dist (D'.target.pts 0) (D'.target.pts 1) = D'.target.oppLen 2 from rfl,
      hO2', hscale, hσR, hf_cast, he_cast, hσb_R]
    field_simp
  have hσf' : (σn : ℝ) * dist (D3.target.pts 2) (D3.target.pts 0)
      = (f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    rw [hD3p2, hD3p0, hdist, show dist (D'.target.pts 1) (D'.target.pts 2) = D'.target.oppLen 0 from rfl,
      hO0, hscale, hσR, hf_cast, he_cast, hσb_R]
    field_simp
  obtain ⟨N', D4, h4c, h40, h41, h42⟩ := ra_tiled e_n f_n σn he_pos hef_lt hσn_pos D3 hσf hσe hσf'
    hm0 hm1 hm2
  exact ⟨e_n, f_n, he_pos, hef_lt, hcop_nat, N', D4, h4c, h40, h41, h42⟩

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.raStatement_of_inst
