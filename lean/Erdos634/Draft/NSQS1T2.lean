/-
Draft/NSQS1T2.lean -- the S1 leaf `S1t2Chk`: `S1tChk` (`2 t p < q`, `cor:ebelow(b)`) PLUS the equality instance `p = 1`, `q = 2 t`
(`T_t(1, 2t)`, i.e. `N = t^2 (12 t^2 - 1)`), killed by `SideRun.no_dissection_T_half` (`2M = f`, `e = 1`; the case `2M <= f` is
`SideRun.not_betaTilable_e1_le_half`).  `S1t2Free N`: every `t >= 2`, coprime `0 < p < q` with `N = t^2 (3 q^2 - p^2)` has
`2 t p < q` or (`p = 1`, `q = 2 t`).  `s1t2Closed_of_free : S1t2Free N -> S1Closed N`.  `S1tChk N -> S1t2Chk N`.
The proof of `s1t2_false_of_arith` is `NSQS1T.s1t_false_of_arith` with one more case in the last branch (copied; NSQS1T untouched).
Credit: Beeson-Rosu (T_M targets), Paliy, the GAP4 analysis (Theorem 3).  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQS1T
import Erdos634.Draft.SideRunHalf

namespace Erdos634.Draft.NSQS1T2

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Realizable Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeS1Arith
open Erdos634.Draft.NSQS1 Erdos634.Draft.NSQChk Erdos634.Draft.AllNExclusion
open Erdos634.Draft.ScaleBaseBetaFull in
set_option maxHeartbeats 4000000 in
theorem s1t2_false_of_arith (N : ℕ)
    (hA : ∀ p q M : ℤ, 0 < p → p < q → IsCoprime p q → 0 < M →
      (N : ℤ) * (p + q) ^ 2 = M ^ 2 * (3 * q ^ 2 - p ^ 2) →
      ∃ t : ℤ, 0 < t ∧ M = t * (p + q) ∧ (t = 1 ∨ (2 ≤ t ∧ (2 * t * p < q ∨ (p = 1 ∧ q = 2 * t)))))
    (D : CongruentDissection N) (α β a b c : ℝ) (r : ℚ) (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi)
    (hmod : D.model.ThreeAlphaData α β a b c) (har : a = (r : ℝ) * c)
    (hbr : b = (1 - (r : ℝ) ^ 2) * c) (htgt : TgtAngles D β β (3 * α)) : False := by
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
  obtain ⟨t, ht0, hMeq, ht⟩ := hA p_i q_i M hp_pos hp_lt_q hcop_pq hM0 hquad_int
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
  have hX_cq : X = c * (t : ℝ) * (q_i : ℝ) := by
    have hMeq_r : (M : ℝ) = (t : ℝ) * ((p_i : ℝ) + q_i) := by exact_mod_cast hMeq
    have hpq_ne : (p_i : ℝ) + (q_i : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hpq_pos)
    have h1 : (t : ℝ) * ((p_i : ℝ) + q_i) * c = X * (1 + (p_i : ℝ) / q_i) := by
      have := hMleg; rw [hMeq_r, hsr, hr_pq] at this; exact this
    have h2 : ((p_i : ℝ) + q_i) * (X - c * t * q_i) = 0 := by
      field_simp at h1; linarith
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h hpq_ne
    · linarith
  have hX_eq : scale_r * X = (t : ℝ) * (f_n : ℝ) ^ 3 := by
    rw [show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hX_cq, hf_cast]
    field_simp
  have hhe : (0 : ℝ) < (e_n : ℝ) := by exact_mod_cast he_pos
  have hhef : (e_n : ℝ) < (f_n : ℝ) := by exact_mod_cast hef_lt
  have hbaseLen : baseLen (e_n : ℝ) f_n = (e_n : ℝ) * (3 * (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2) := by
    unfold baseLen Nq; ring
  -- Distances in D''.target (scaled by scale_r from D'.target)
  -- oppLen 2 T = dist (T.pts 0) (T.pts 1), oppLen 0 T = dist (T.pts 1) (T.pts 2),
  -- oppLen 1 T = dist (T.pts 2) (T.pts 0) — all rfl in Fin 3
  have hd01 : dist (D''.target.pts 0) (D''.target.pts 1) = (t : ℝ) * baseLen (e_n : ℝ) f_n := by
    rw [hD''_tpts 0, hD''_tpts 1, homothetyEquiv_dist, abs_of_pos hscale_pos,
        show dist (D'.target.pts 0) (D'.target.pts 1) = D'.target.oppLen 2 from rfl]
    rw [hYs, hX_cq, show scale_r = (f_n : ℝ) ^ 2 / c from rfl, hsr, hr_pq, he_cast, hf_cast]
    unfold baseLen Nq; field_simp
  have hd12 : dist (D''.target.pts 1) (D''.target.pts 2) = (t : ℝ) * (f_n : ℝ) ^ 3 := by
    have : dist (D''.target.pts 1) (D''.target.pts 2) = scale_r * X := by
      rw [hD''_tpts 1, hD''_tpts 2, homothetyEquiv_dist, abs_of_pos hscale_pos,
          show dist (D'.target.pts 1) (D'.target.pts 2) = X from rfl]
    rw [this, hX_eq]
  have hd20 : dist (D''.target.pts 2) (D''.target.pts 0) = (t : ℝ) * (f_n : ℝ) ^ 3 := by
    have : dist (D''.target.pts 2) (D''.target.pts 0) = scale_r * X := by
      rw [hD''_tpts 2, hD''_tpts 0, homothetyEquiv_dist, abs_of_pos hscale_pos,
          show dist (D'.target.pts 2) (D'.target.pts 0) = D'.target.oppLen 1 from rfl,
          hX1]
    rw [this, hX_eq]
  rcases ht with h1 | ⟨h2, h2pp⟩
  · subst h1
    simp only [Int.cast_one, one_mul] at hd01 hd12 hd20
    have htgt_cong : D''.target.Congruent
        (baseBetaTarget (e_n : ℝ) f_n (by exact_mod_cast he_pos) (by exact_mod_cast hef_lt)) :=
      SssCongruent.congruent_of_dist_three
        (by rw [hd01, baseBetaTarget_dist_base hhe hhef]; exact hbaseLen)
        (by rw [hd12, baseBetaTarget_dist_leg₁ hhe hhef])
        (by rw [hd20, dist_comm, baseBetaTarget_dist_leg₀ hhe hhef])
    exact not_baseBetaTiled ⟨e_n, f_n, he_pos, hef_lt, hcop_nat, N, D'', htgt_cong, hm0, hm1, hm2⟩
  · obtain ⟨tn, rfl⟩ := Int.eq_ofNat_of_zero_le ht0.le
    rcases h2pp with h2p | ⟨hp1, hq2⟩
    · have hlt : 2 * tn * e_n < f_n := by
        have : (2 * (tn : ℤ) * p_i) < q_i := h2p
        rw [← he_int, ← hf_int] at this
        exact_mod_cast this
      refine Erdos634.Draft.SideRunG.ebelow_b e_n f_n tn he_pos hef_lt hcop_nat (by omega) hlt D'' ?_ ?_
      · refine ⟨1, ?_, ?_, ?_⟩ <;> simp only [Int.cast_natCast] at hd01 hd12 hd20
        · simpa using hd12
        · simpa using hd20
        · rw [show (1 : Equiv.Perm (Fin 3)) 0 = 0 from rfl, show (1 : Equiv.Perm (Fin 3)) 1 = 1 from rfl]
          rw [hd01, hbaseLen]
      · refine ⟨1, ?_, ?_, ?_⟩
        · exact hm0
        · exact hm1
        · exact hm2
    · -- the equality case p = 1, q = 2 t: T_t(1, 2t), no tiling by `no_dissection_T_half` (`2M = f`)
      have he1 : e_n = 1 := by
        have : (e_n : ℤ) = 1 := by rw [he_int]; exact hp1
        exact_mod_cast this
      have hf2 : 2 * tn = f_n := by
        have : (f_n : ℤ) = 2 * (tn : ℤ) := by rw [hf_int]; exact hq2
        omega
      have he1r : (e_n : ℝ) = 1 := by exact_mod_cast he1
      refine Erdos634.Draft.SideRun.no_dissection_T_half f_n tn (by omega) hf2 D'' ?_ ?_
      · refine ⟨1, ?_, ?_, ?_⟩ <;> simp only [Int.cast_natCast] at hd01 hd12 hd20
        · simpa using hd12
        · simpa using hd20
        · rw [show (1 : Equiv.Perm (Fin 3)) 0 = 0 from rfl, show (1 : Equiv.Perm (Fin 3)) 1 = 1 from rfl]
          rw [hd01, hbaseLen, he1r]; ring
      · refine ⟨1, ?_, ?_, ?_⟩
        · refine hm0.trans ?_; rw [he1r]; ring
        · refine hm1.trans ?_; rw [he1r]; ring
        · exact hm2



/-- `S1t2Free N`: S1 hypothesis with the equality instance. -/
def S1t2Free (N : ℕ) : Prop :=
  ∀ t p q : ℤ, 2 ≤ t → 0 < p → p < q → IsCoprime p q → (N : ℤ) = t ^ 2 * (3 * q ^ 2 - p ^ 2) →
    2 * t * p < q ∨ (p = 1 ∧ q = 2 * t)

theorem s1t2Closed_of_free (N : ℕ) (h : S1t2Free N) : S1Closed N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  refine s1t2_false_of_arith N ?_ D α β a b c r hα hrel hmod har hbr htgt
  intro p q M hp hpq hcop hM heq
  obtain ⟨t, ht, hMt, hNt⟩ := s1_arith_t hp hpq hcop hM heq
  by_cases h1 : t = 1
  · exact ⟨t, ht, hMt, Or.inl h1⟩
  · exact ⟨t, ht, hMt, Or.inr ⟨by omega, h t p q (by omega) hp hpq hcop hNt⟩⟩

/-- The executable leaf: no `t >= 2`, `p < q` coprime, `q <= 2 t p`, other than `p = 1`, `q = 2 t`. -/
def S1t2Chk (N : ℕ) : Prop :=
  ∀ t ≤ N, 2 ≤ t → t * t ∣ N → ∀ q ≤ N, N / (t * t) ≤ 3 * q * q →
    ¬ (sqChk (3 * q * q - N / (t * t)) ∧ 0 < Nat.sqrt (3 * q * q - N / (t * t)) ∧
       Nat.sqrt (3 * q * q - N / (t * t)) < q ∧ Nat.Coprime (Nat.sqrt (3 * q * q - N / (t * t))) q ∧
       q ≤ 2 * t * Nat.sqrt (3 * q * q - N / (t * t)) ∧
       ¬ (Nat.sqrt (3 * q * q - N / (t * t)) = 1 ∧ q = 2 * t))

set_option synthInstance.maxSize 20000 in
set_option synthInstance.maxHeartbeats 2000000 in
instance (N : ℕ) : Decidable (S1t2Chk N) := by unfold S1t2Chk sqChk; infer_instance

theorem s1t2Free_of_chk {N : ℕ} (h : S1t2Chk N) : S1t2Free N := by
  intro t p q ht hp hpq hcop hN
  by_contra hcon
  push Not at hcon
  obtain ⟨hcon, hcon2⟩ := hcon
  lift t to ℕ using (by omega)
  lift p to ℕ using hp.le
  lift q to ℕ using (by omega)
  have hN' : N = t * t * (3 * q * q - p * p) := by
    have hle : p * p ≤ 3 * q * q := by
      have : (p : ℤ) < q := hpq
      have : p < q := by exact_mod_cast this
      nlinarith
    have : (N : ℤ) = ((t * t * (3 * q * q - p * p) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]; rw [hN]; ring
    exact_mod_cast this
  have hpq' : p < q := by exact_mod_cast hpq
  have hp' : 0 < p := by exact_mod_cast hp
  have ht2 : 2 ≤ t := by exact_mod_cast ht
  have hpp : p * p < q * q := Nat.mul_self_lt_mul_self hpq'
  have hqq : q ≤ q * q := Nat.le_mul_self q
  have hYpos : 0 < 3 * q * q - p * p := by
    apply Nat.sub_pos_of_lt; nlinarith
  have hYq : q ≤ 3 * q * q - p * p := Nat.le_sub_of_add_le (by nlinarith)
  have hdiv : N / (t * t) = 3 * q * q - p * p := by
    rw [hN']; exact Nat.mul_div_cancel_left _ (by positivity)
  have htt : t * t ∣ N := ⟨_, hN'⟩
  have htN : t ≤ N := by
    have : t * t ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_right _ hYpos
    nlinarith
  have hqN : q ≤ N := by
    have h1 : t * t ≥ 1 := by nlinarith
    have : 3 * q * q - p * p ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hle : N / (t * t) ≤ 3 * q * q := by rw [hdiv]; omega
  have hsub : 3 * q * q - N / (t * t) = p * p := by rw [hdiv]; omega
  apply h t htN ht2 htt q hqN hle
  rw [hsub, Nat.sqrt_eq]
  refine ⟨?_, hp', hpq', ?_, ?_, ?_⟩
  · unfold sqChk; rw [Nat.sqrt_eq]
  · have : Int.gcd (p : ℤ) (q : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simpa [Int.gcd_natCast_natCast] using this
  · exact_mod_cast hcon
  · rintro ⟨h1, h2⟩
    exact hcon2 (by exact_mod_cast h1) (by exact_mod_cast h2)

end Erdos634.Draft.NSQS1T2

#print axioms Erdos634.Draft.NSQS1T2.s1t2_false_of_arith
#print axioms Erdos634.Draft.NSQS1T2.s1t2Closed_of_free
#print axioms Erdos634.Draft.NSQS1T2.s1t2Free_of_chk
