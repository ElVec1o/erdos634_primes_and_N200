/-
Draft/NSQRWT2.lean -- R-W (S4) with the S+ kill for the thick members.  Same as `NSQRWT` (copy of its proof body, existing files untouched)
but `RWFreeT2 N` additionally excuses the instances `2 <= e`, `S' < f`, `S' (f-e) <= e+1` (with `f <= S' e`, `e < S'(f-e)`), which are closed by
`SplusThick.wTilable_not_of_small_M`'s proof body (`small_M_D`, via `thickw_count_tiling_thick` and `no_rep_z_ge`).  `RWChkT2` is the decidable form.
Credit: Beeson-Rosu (framework, W_M), Paliy (S4/thick work), the S+ analysis (z >= e+1 corner run; M<f, M(f-e)<f arithmetic).
UNAUDITED.  Formalization debt, NOT /goal progress.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQRWT
import Erdos634.Draft.SplusThickFinal

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RWPieces Erdos634.Draft.RWAssemble Erdos634.CertCoord
  Erdos634.Draft.NSQRW

namespace Erdos634.Draft.NSQRWT2

open Erdos634.Draft.NSQChk Erdos634.Draft.AllNExclusion

def RWFreeT2 (N : ℕ) : Prop :=
  ∀ S' e f : ℤ, 2 ≤ S' → 0 < e → e < f → IsCoprime e f → (N : ℤ) = S' ^ 2 * (2 * f ^ 2 - e ^ 2) →
    f ≤ S' * e → e < S' * (f - e) → ¬ (2 ≤ e ∧ S' < f ∧ S' * (f - e) ≤ e + 1) → False

/-- the S+ kill (`SplusThick.wTilable_not_of_small_M`), stated for an arbitrary congruent dissection (`N` free):
`W_M(e,f)` is not tiled when `2 <= e < f`, `M < f`, `f <= M e`, `M (f - e) <= e + 1`.  Same proof body as
`wTilable_not_of_small_M`. -/
theorem small_M_D {N : ℕ} (e f M : ℕ) (hco : Nat.Coprime e f) (he : 2 ≤ e) (hef : e < f)
    (hMf : M < f) (hfM : f ≤ M * e) (hMfe : M * (f - e) ≤ e + 1) (D₀ : CongruentDissection N)
    (hT : Erdos634.Draft.FDBBaseBetaE1.HasSides D₀.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : Erdos634.Draft.FDBBaseBetaE1.HasSides D₀.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    False := by
  have hM : 1 ≤ M := by
    rcases Nat.eq_zero_or_pos M with h | h
    · subst h; omega
    · exact h
  obtain ⟨x, y, z, hN, hz1, hz2⟩ := Erdos634.Draft.SplusThick.thickw_count_tiling_thick e f M (by omega) hef hco hM D₀ hT hMod
  exact Erdos634.Draft.SplusThick.no_rep_z_ge (by omega) hef hco hMf hMfe hN hz1 hz2

section Cl
open scoped Classical

set_option maxHeartbeats 4000000 in
theorem rwStatement_nsqT2 (N : ℕ) (hRW : RWFreeT2 N) : RWStatementNsq N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  -- Step 0: relabel the target so its angles are (2α, β, α+β) at vertices 0, 1, 2
  obtain ⟨σ_t, ht0, ht1, ht2⟩ := htgt
  set D' := D.relabelTarget' σ_t
  have hD'_tgt_pts : ∀ k, D'.target.pts k = D.target.pts (σ_t k) := fun _ => rfl
  have hP0 : D'.target.angleAt 0 = 2 * α :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 0).trans ht0
  have hP1 : D'.target.angleAt 1 = β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 1).trans ht1
  have hP2 : D'.target.angleAt 2 = α + β :=
    (Row14AnyLabel.angleAt_of_pts σ_t hD'_tgt_pts 2).trans ht2
  -- Step 1: Row 14
  obtain ⟨s, S, hs0, hs1, hc, ha_sc, hb_sc, hO1, hSc, hquad⟩ :=
    Row14.setup D' hα hrel hmod hP0 hP1 hP2
  have hsr : s = (r : ℝ) := mul_right_cancel₀ hc.ne' (by rw [← ha_sc, ← har])
  set p_i := r.num
  set q_i : ℤ := (r.den : ℤ)
  have hq_pos : (0 : ℤ) < q_i := by show (0 : ℤ) < (r.den : ℤ); exact_mod_cast r.pos
  have hcop_pq : IsCoprime p_i q_i := by
    rw [Int.isCoprime_iff_gcd_eq_one]; exact_mod_cast r.reduced
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
  -- Step 2: the integer equation
  have hEq : (N : ℤ) * p_i ^ 2 = S ^ 2 * (2 * q_i ^ 2 - p_i ^ 2) := by
    have hq2 : (q_i : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hq_r
    have h1 := hquad; rw [hsr, hr_pq] at h1
    have h2 : (N : ℝ) * (p_i : ℝ) ^ 2 = (S : ℝ) ^ 2 * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) := by
      field_simp at h1; linarith
    exact_mod_cast h2
  -- Step 3: S > 0
  have hO2pos : 0 < D'.target.oppLen 2 := Row3.RP.oppLen_pos D'.target 2
  have hSpos : 0 < S := by
    have : (0 : ℝ) < (S : ℝ) * c := by rw [hSc]; exact mul_pos hs0 hO2pos
    have : (0 : ℝ) < (S : ℝ) := by
      by_contra hle; push Not at hle; nlinarith
    exact_mod_cast this
  -- Step 4: S' kept
  obtain ⟨S', hS'pos, hNS', hSS'⟩ := w_arith_nsq (by have := D.pos; omega) hp_pos hp_lt_q hcop_pq hSpos hEq
  have hSR : (S : ℝ) = (S' : ℝ) * (p_i : ℝ) := by rw [hSS']; push_cast; ring
  have hpR : (0 : ℝ) < (p_i : ℝ) := by exact_mod_cast hp_pos
  have hS'R0 : (0 : ℝ) < (S' : ℝ) := by exact_mod_cast hS'pos
  obtain ⟨c1, hc1⟩ : ∃ c1 : ℝ, c1 = (S' : ℝ) * c := ⟨_, rfl⟩
  have hc1pos : 0 < c1 := by rw [hc1]; positivity
  -- Step 5: the target's sides
  have hO2 : D'.target.oppLen 2 = (q_i : ℝ) * c1 := by
    have h1 := hSc; rw [hSR, hsr, hr_pq] at h1
    field_simp at h1
    rw [hc1]; linarith
  have hO1 : D'.target.oppLen 1 = ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c1 / q_i := by
    rw [hO1, hO2, hsr, hr_pq]; field_simp
  -- cos α from the model
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hmod
  have hcosA : 2 * b * c * Real.cos α = b ^ 2 + c ^ 2 - a ^ 2 := by
    have := cos_angleAt_sym D.model (σm 0) (σm 1) (σm 2) (perm_adj σm)
    rw [hα0m, ham, hbm, hcm] at this
    exact this
  have hcosα : Real.cos α = (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / (2 * (q_i : ℝ) ^ 2) := by
    have hb' : b = (1 - s ^ 2) * c := hb_sc
    have ha' : a = s * c := ha_sc
    have hs' : s = (p_i : ℝ) / q_i := by rw [hsr, hr_pq]
    have h1 : (1 - s ^ 2) ≠ 0 := by nlinarith
    rw [hb', ha'] at hcosA
    have h2 : c ^ 2 * (1 - s ^ 2) * (2 * Real.cos α - (2 - s ^ 2)) = 0 := by nlinarith [hcosA]
    have h3 : Real.cos α = (2 - s ^ 2) / 2 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h (mul_ne_zero (pow_ne_zero 2 hc.ne') h1)
      · linarith
    rw [h3, hs']; field_simp
  -- O0 by the law of cosines at target vertex 0
  have hO0 : D'.target.oppLen 0 = (p_i : ℝ) * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c1 / (q_i : ℝ) ^ 2 := by
    have hcl := cos_angleAt_mul D'.target 0
    rw [show (0 : Fin 3) + 1 = 1 from rfl, show (0 : Fin 3) + 2 = 2 from rfl, hP0,
      Real.cos_two_mul, hcosα, hO1, hO2] at hcl
    have hO0pos : 0 < D'.target.oppLen 0 := Row3.RP.oppLen_pos D'.target 0
    have hsq : D'.target.oppLen 0 ^ 2
        = ((p_i : ℝ) * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c1 / (q_i : ℝ) ^ 2) ^ 2 := by
      field_simp at hcl ⊢
      nlinarith [hcl]
    have hrhs : 0 ≤ (p_i : ℝ) * (2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c1 / (q_i : ℝ) ^ 2 := by
      have : (0 : ℝ) < 2 * (q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2 := by
        have : (p_i : ℝ) < q_i := by exact_mod_cast hp_lt_q
        nlinarith
      positivity
    exact RWPieces.eq_of_sq_eq hO0pos.le hrhs hsq
  -- Step 6: natural-number parameters
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
  -- Step 7: scale by f²/c and relabel the model
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
  -- Step 8: target congruent to the west piece W₁
  have hhe : (0 : ℝ) < (e_n : ℝ) := by exact_mod_cast he_pos
  have hhef : (e_n : ℝ) < (f_n : ℝ) := by exact_mod_cast hef_lt
  have hD''_tpts : ∀ k, D''.target.pts k =
      homothetyEquiv (D'.model.pts 0) scale_r hscale_pos.ne' (D'.target.pts k) := fun _ => rfl
  have hd01 : dist (D''.target.pts 0) (D''.target.pts 1) = (S' : ℝ) * (f_n : ℝ) ^ 3 := by
    rw [hD''_tpts 0, hD''_tpts 1, homothetyEquiv_dist, abs_of_pos hscale_pos,
      show dist (D'.target.pts 0) (D'.target.pts 1) = D'.target.oppLen 2 from rfl, hO2, hscale,
      hf_cast]
    rw [hc1]; field_simp; try ring
  have hd12 : dist (D''.target.pts 1) (D''.target.pts 2)
      = (S' : ℝ) * ((e_n : ℝ) * (2 * (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2)) := by
    rw [hD''_tpts 1, hD''_tpts 2, homothetyEquiv_dist, abs_of_pos hscale_pos,
      show dist (D'.target.pts 1) (D'.target.pts 2) = D'.target.oppLen 0 from rfl, hO0, hscale,
      hf_cast, he_cast]
    rw [hc1]; field_simp; try ring
  have hd20 : dist (D''.target.pts 2) (D''.target.pts 0)
      = (S' : ℝ) * ((f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2)) := by
    rw [hD''_tpts 2, hD''_tpts 0, homothetyEquiv_dist, abs_of_pos hscale_pos,
      show dist (D'.target.pts 2) (D'.target.pts 0) = D'.target.oppLen 1 from rfl, hO1, hscale,
      hf_cast, he_cast]
    rw [hc1]; field_simp; try ring
  by_cases hS'1 : S' = 1
  · have hS'R1 : (S' : ℝ) = 1 := by rw [hS'1]; norm_num
    rw [hS'R1, one_mul] at hd01 hd12 hd20
    have hcong : D''.target.Congruent (wTri (e := (e_n : ℝ)) (f := (f_n : ℝ)) hhe hhef) := by
      refine SssCongruent.congruent_of_dist_three ?_ ?_ ?_
      · rw [hd01]
        show (f_n : ℝ) ^ 3 = dist (mkPt (baseLen (e_n : ℝ) f_n / 2) (height (e_n : ℝ) f_n)) (mkPt 0 0)
        rw [d_AW hhe hhef]
      · rw [hd12]
        show (e_n : ℝ) * (2 * (f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2)
          = dist (mkPt 0 0) (mkPt (xP (e_n : ℝ) f_n) 0)
        rw [d_WP hhe hhef]
      · rw [hd20]
        show (f_n : ℝ) * ((f_n : ℝ) ^ 2 - (e_n : ℝ) ^ 2)
          = dist (mkPt (xP (e_n : ℝ) f_n) 0) (mkPt (baseLen (e_n : ℝ) f_n / 2) (height (e_n : ℝ) f_n))
        rw [dist_comm, d_AP hhe hhef]
    obtain ⟨N', D3, h3c, h30, h31, h32⟩ := rw_tiled e_n f_n he_pos hef_lt D'' hcong hm0 hm1 hm2
    exact ⟨e_n, f_n, he_pos, hef_lt, hcop_nat, N', D3, h3c, h30, h31, h32⟩

  · exfalso
    have hS'2 : 2 ≤ S' := by omega
    by_cases hk0 : S' * p_i < q_i
    · set Sn : ℕ := S'.natAbs with hSn
      have hSn_int : (Sn : ℤ) = S' := Int.natAbs_of_nonneg hS'pos.le
      have hSn_cast : (Sn : ℝ) = (S' : ℝ) := by exact_mod_cast hSn_int
      have hSn1 : 1 ≤ Sn := by omega
      have hMe : Sn * e_n < f_n := by
        have h1 : (Sn : ℤ) * (e_n : ℤ) < (f_n : ℤ) := by rw [hSn_int, he_int, hf_int]; exact hk0
        exact_mod_cast h1
      have s0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := Equiv.swap_apply_left _ _
      have s1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := Equiv.swap_apply_right _ _
      have s2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      refine Erdos634.Draft.SideRunG.ebelow_a e_n f_n Sn he_pos hef_lt hcop_nat hSn1 hMe D'' ?_ ?_
      · rw [hSn_cast]
        unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
        refine ⟨Equiv.swap 0 1, ?_, ?_, ?_⟩
        · rw [s1, s2, dist_comm]; exact hd20
        · rw [s2, s0, dist_comm]; exact hd12
        · rw [s0, s1, dist_comm]; exact hd01
      · unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
        exact ⟨Equiv.refl _, hm0, hm1, hm2⟩
    by_cases hk : S' * (q_i - p_i) ≤ p_i
    · set Sn : ℕ := S'.natAbs with hSn
      have hSn_int : (Sn : ℤ) = S' := Int.natAbs_of_nonneg hS'pos.le
      have hSn_cast : (Sn : ℝ) = (S' : ℝ) := by exact_mod_cast hSn_int
      have hSn1 : 1 ≤ Sn := by omega
      have hMe : Sn * (f_n - e_n) ≤ e_n := by
        have h1 : (Sn : ℤ) * ((f_n : ℤ) - (e_n : ℤ)) ≤ (e_n : ℤ) := by
          rw [hSn_int, he_int, hf_int]; exact hk
        have h2 : (Sn : ℤ) * (((f_n - e_n : ℕ)) : ℤ) ≤ (e_n : ℤ) := by
          rw [Nat.cast_sub hef_lt.le]; exact h1
        exact_mod_cast h2
      have s0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := Equiv.swap_apply_left _ _
      have s1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := Equiv.swap_apply_right _ _
      have s2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      refine Erdos634.Draft.SideRunGA.thickw_a e_n f_n Sn he_pos hef_lt hcop_nat hSn1 hMe D'' ?_ ?_
      · rw [hSn_cast]
        unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
        refine ⟨Equiv.swap 0 1, ?_, ?_, ?_⟩
        · rw [s1, s2, dist_comm]; exact hd20
        · rw [s2, s0, dist_comm]; exact hd12
        · rw [s0, s1, dist_comm]; exact hd01
      · unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
        exact ⟨Equiv.refl _, hm0, hm1, hm2⟩
    by_cases hnew : 2 ≤ p_i ∧ S' < q_i ∧ S' * (q_i - p_i) ≤ p_i + 1
    · obtain ⟨hp2, hSq, hSk⟩ := hnew
      set Sn : ℕ := S'.natAbs with hSn
      have hSn_int : (Sn : ℤ) = S' := Int.natAbs_of_nonneg hS'pos.le
      have hSn_cast : (Sn : ℝ) = (S' : ℝ) := by exact_mod_cast hSn_int
      have hSn1 : 1 ≤ Sn := by omega
      have hfM : f_n ≤ Sn * e_n := by
        have h1 : (f_n : ℤ) ≤ (Sn : ℤ) * (e_n : ℤ) := by rw [hSn_int, he_int, hf_int]; exact not_lt.mp hk0
        exact_mod_cast h1
      have hMf : Sn < f_n := by
        have h1 : (Sn : ℤ) < (f_n : ℤ) := by rw [hSn_int, hf_int]; exact hSq
        exact_mod_cast h1
      have he2 : 2 ≤ e_n := by
        have h1 : (2 : ℤ) ≤ (e_n : ℤ) := by rw [he_int]; exact hp2
        exact_mod_cast h1
      have hMfe : Sn * (f_n - e_n) ≤ e_n + 1 := by
        have h1 : (Sn : ℤ) * ((f_n : ℤ) - (e_n : ℤ)) ≤ (e_n : ℤ) + 1 := by
          rw [hSn_int, he_int, hf_int]; exact hSk
        have h2 : (Sn : ℤ) * (((f_n - e_n : ℕ)) : ℤ) ≤ (e_n : ℤ) + 1 := by
          rw [Nat.cast_sub hef_lt.le]; exact h1
        exact_mod_cast h2
      have s0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := Equiv.swap_apply_left _ _
      have s1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := Equiv.swap_apply_right _ _
      have s2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
      refine Erdos634.Draft.NSQRWT2.small_M_D e_n f_n Sn hcop_nat he2 hef_lt hMf hfM hMfe D'' ?_ ?_
      · rw [hSn_cast]
        unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
        refine ⟨Equiv.swap 0 1, ?_, ?_, ?_⟩
        · rw [s1, s2, dist_comm]; exact hd20
        · rw [s2, s0, dist_comm]; exact hd12
        · rw [s0, s1, dist_comm]; exact hd01
      · unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
        exact ⟨Equiv.refl _, hm0, hm1, hm2⟩
    · exact hRW S' p_i q_i hS'2 hp_pos hp_lt_q hcop_pq hNS' (not_lt.mp hk0) (not_le.mp hk) hnew

end Cl

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

def RWChkT2 (N : ℕ) : Prop :=
  ∀ s ≤ N, 2 ≤ s → s * s ∣ N → ∀ f ≤ N, N / (s * s) ≤ 2 * f * f →
    ¬ (sqChk (2 * f * f - N / (s * s)) ∧ 0 < Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < f ∧ Nat.Coprime (Nat.sqrt (2 * f * f - N / (s * s))) f ∧
       f ≤ s * Nat.sqrt (2 * f * f - N / (s * s)) ∧
       Nat.sqrt (2 * f * f - N / (s * s)) < s * (f - Nat.sqrt (2 * f * f - N / (s * s))) ∧
       ¬ (2 ≤ Nat.sqrt (2 * f * f - N / (s * s)) ∧ s < f ∧
          s * (f - Nat.sqrt (2 * f * f - N / (s * s))) ≤ Nat.sqrt (2 * f * f - N / (s * s)) + 1))

instance (N : ℕ) : Decidable (RWChkT2 N) := by unfold RWChkT2 sqChk; infer_instance

theorem rwFreeT2_of_chk {N : ℕ} (h : RWChkT2 N) : RWFreeT2 N := by
  intro s e f hs he hef hcop hN hk0 hk hnew
  lift s to ℕ using (by omega)
  lift e to ℕ using he.le
  lift f to ℕ using (by omega)
  have hef' : e < f := by exact_mod_cast hef
  have he' : 0 < e := by exact_mod_cast he
  have hs2 : 2 ≤ s := by exact_mod_cast hs
  have hle : e * e ≤ 2 * f * f := by nlinarith
  have hN' : N = s * s * (2 * f * f - e * e) := by
    have : (N : ℤ) = ((s * s * (2 * f * f - e * e) : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]; rw [hN]; ring
    exact_mod_cast this
  have hee : e * e < f * f := Nat.mul_self_lt_mul_self hef'
  have hff : f ≤ f * f := Nat.le_mul_self f
  have hYpos : 0 < 2 * f * f - e * e := by
    apply Nat.sub_pos_of_lt; nlinarith
  have hYf : f ≤ 2 * f * f - e * e := Nat.le_sub_of_add_le (by nlinarith)
  have hdiv : N / (s * s) = 2 * f * f - e * e := by
    rw [hN']; exact Nat.mul_div_cancel_left _ (by positivity)
  have hss : s * s ∣ N := ⟨_, hN'⟩
  have hsN : s ≤ N := by
    have : s * s ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_right _ hYpos
    nlinarith
  have hfN : f ≤ N := by
    have h1 : s * s ≥ 1 := by nlinarith
    have : 2 * f * f - e * e ≤ N := by rw [hN']; exact Nat.le_mul_of_pos_left _ (by positivity)
    omega
  have hle2 : N / (s * s) ≤ 2 * f * f := by rw [hdiv]; omega
  have hsub : 2 * f * f - N / (s * s) = e * e := by rw [hdiv]; omega
  apply h s hsN hs2 hss f hfN hle2
  rw [hsub, Nat.sqrt_eq]
  refine ⟨?_, he', hef', ?_, ?_, ?_, ?_⟩
  · unfold sqChk; rw [Nat.sqrt_eq]
  · have : Int.gcd (e : ℤ) (f : ℤ) = 1 := Int.isCoprime_iff_gcd_eq_one.mp hcop
    simpa [Int.gcd_natCast_natCast] using this
  · have h1 : (f : ℤ) ≤ (s : ℤ) * (e : ℤ) := hk0
    exact_mod_cast h1
  · have h1 : (e : ℤ) < (s : ℤ) * (((f - e : ℕ)) : ℤ) := by rw [Nat.cast_sub hef'.le]; exact hk
    exact_mod_cast h1
  · rintro ⟨h2, h3, h4⟩
    apply hnew
    refine ⟨by exact_mod_cast h2, by exact_mod_cast h3, ?_⟩
    have h5 : (s : ℤ) * (((f - e : ℕ)) : ℤ) ≤ (e : ℤ) + 1 := by exact_mod_cast h4
    rw [Nat.cast_sub hef'.le] at h5
    exact h5

end Erdos634.Draft.NSQRWT2

#print axioms Erdos634.Draft.NSQRWT2.rwStatement_nsqT2
#print axioms Erdos634.Draft.NSQRWT2.rwFreeT2_of_chk
