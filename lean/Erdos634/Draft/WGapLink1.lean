/-
Draft/WGapLink1.lean -- 16 November 2026 (work item internal working notes).  UNAUDITED beyond internal checks.  Not imported by any aggregate.  Leaf module.
Closes link 6 of internal working notes the step "a congruent dissection of S4 shape for `N` gives `WTilable e f M`" as a STATED lemma.
* `s4_wTilable`: for a `CongruentDissection N` with the hypotheses of `NSQRW.RWStatementNsq N` (three-alpha data, `a = r c`, `b = (1-r^2) c`, target angles `(2α, β, α+β)`),
  there are naturals `0 < e < f` coprime and `M >= 1` with `N = (2 f^2 - e^2) M^2` and `CollarG.WTilable e f M`.  The proof text is steps 0-8 of
  `NSQRWT2.rwStatement_nsqT2` (copied; that file is untouched); the only new step is the cast of `D''` to `CongruentDissection ((2 f^2-e^2) M^2)` (`wTilable_of_eq`).
* `RWFreeW N`, `rwStatement_nsqW`: the S4 leaf with the W-gap window added: a representation `(e,f,M)` of `N` is excused when `M e < f` (`SideRunG.not_wTilable_ebelow`; this includes
  `M = 1`) or when it lies in the W-gap window (`WGapRung.no_tiling_W_gap`).  `rwStatement_nsqW : RWFreeW N -> RWStatementNsq N` plugs into `chain_nsq` in place of `rwStatement_nsqT2 N (rwFreeT2_of_chk _)`.
Credit: Beeson-Rosu (framework, W_M), Paliy (S4/thick work), the S+ work item, the W-gap proof of this project.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQRWT2
import Erdos634.Draft.WGapStation4

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RWPieces Erdos634.Draft.RWAssemble Erdos634.CertCoord
  Erdos634.Draft.NSQRW

namespace Erdos634.Draft.WGapLink1

open Erdos634.Draft.NSQChk Erdos634.Draft.AllNExclusion

/-- transport of a dissection along `N = (2 f^2 - e^2) M^2`, giving the project predicate `WTilable` -/
theorem wTilable_of_eq {N : ℕ} (e f M : ℕ) (hN : N = (2 * f ^ 2 - e ^ 2) * M ^ 2) (D : CongruentDissection N)
    (hT : Erdos634.Draft.FDBBaseBetaE1.HasSides D.target ((M : ℝ) * ((f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2)))
      ((M : ℝ) * ((e : ℝ) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))) ((M : ℝ) * (f : ℝ) ^ 3))
    (hMod : Erdos634.Draft.FDBBaseBetaE1.HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) :
    Erdos634.Draft.CollarG.WTilable e f M := by
  subst hN
  exact ⟨D, hT, hMod⟩

section Cl
open scoped Classical

set_option maxHeartbeats 4000000 in
/-- **link 6 (S4 shape -> `WTilable`)** -/
theorem s4_wTilable (N : ℕ) (D : CongruentDissection N)
    (α β a b c : ℝ) (r : ℚ) (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi)
    (hmod : D.model.ThreeAlphaData α β a b c) (har : a = (r : ℝ) * c) (hbr : b = (1 - (r : ℝ) ^ 2) * c)
    (htgt : TgtAngles D (2 * α) β (α + β)) :
    ∃ e f M : ℕ, 0 < e ∧ e < f ∧ Nat.Coprime e f ∧ 1 ≤ M ∧ N = (2 * f ^ 2 - e ^ 2) * M ^ 2 ∧
      Erdos634.Draft.CollarG.WTilable e f M := by
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
  -- NEW (only step not copied): the natural-number equation and the `WTilable` conclusion
  set Sn : ℕ := S'.natAbs with hSn
  have hSn_int : (Sn : ℤ) = S' := Int.natAbs_of_nonneg hS'pos.le
  have hSn_cast : (Sn : ℝ) = (S' : ℝ) := by exact_mod_cast hSn_int
  have hSn1 : 1 ≤ Sn := by omega
  have hle : e_n ^ 2 ≤ 2 * f_n ^ 2 := by nlinarith [hef_lt]
  have hNnat : N = (2 * f_n ^ 2 - e_n ^ 2) * Sn ^ 2 := by
    have h1 : (N : ℤ) = (((2 * f_n ^ 2 - e_n ^ 2) * Sn ^ 2 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub hle]
      rw [hNS', hSn_int, he_int, hf_int]; ring
    exact_mod_cast h1
  have s0 : (Equiv.swap (0 : Fin 3) 1) 0 = 1 := Equiv.swap_apply_left _ _
  have s1 : (Equiv.swap (0 : Fin 3) 1) 1 = 0 := Equiv.swap_apply_right _ _
  have s2 : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
  refine ⟨e_n, f_n, Sn, he_pos, hef_lt, hcop_nat, hSn1, hNnat,
    wTilable_of_eq e_n f_n Sn hNnat D'' ?_ ?_⟩
  · rw [hSn_cast]
    unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
    refine ⟨Equiv.swap 0 1, ?_, ?_, ?_⟩
    · rw [s1, s2, dist_comm]; exact hd20
    · rw [s2, s0, dist_comm]; exact hd12
    · rw [s0, s1, dist_comm]; exact hd01
  · unfold Erdos634.Draft.FDBBaseBetaE1.HasSides
    exact ⟨Equiv.refl _, hm0, hm1, hm2⟩

end Cl

/-- The S4 leaf with the W-gap window: every representation `N = (2 f^2 - e^2) M^2` (`0 < e < f` coprime, `M >= 1`) with `f <= M e` that is NOT in the
W-gap window (`2 <= e` and `M (f - e) < f`) is excluded by hypothesis. -/
def RWFreeW (N : ℕ) : Prop :=
  ∀ M e f : ℕ, 0 < e → e < f → Nat.Coprime e f → 1 ≤ M → N = (2 * f ^ 2 - e ^ 2) * M ^ 2 → f ≤ M * e →
    ¬ (2 ≤ e ∧ M * (f - e) < f) → False

/-- **The S4 leaf, W-gap version.**  Plugs into `NSQMain.chain_nsq` as its `gS4` in place of `rwStatement_nsqT2 N (rwFreeT2_of_chk _)`. -/
theorem rwStatement_nsqW (N : ℕ) (hRW : RWFreeW N) : RWStatementNsq N := by
  intro D α β a b c r hα hrel hmod har hbr htgt
  exfalso
  obtain ⟨e, f, M, he, hef, hco, hM, hN, hW⟩ := s4_wTilable N D α β a b c r hα hrel hmod har hbr htgt
  by_cases h1 : M * e < f
  · exact Erdos634.Draft.SideRunG.not_wTilable_ebelow e f M he hef hco hM h1 hW
  · by_cases hg : 2 ≤ e ∧ M * (f - e) < f
    · exact Erdos634.Draft.WGapRung.no_tiling_W_gap e f M hco hg.1 hef (not_lt.mp h1) hg.2 hW
    · exact hRW M e f he hef hco hM hN (not_lt.mp h1) hg

end Erdos634.Draft.WGapLink1

#print axioms Erdos634.Draft.WGapLink1.wTilable_of_eq
#print axioms Erdos634.Draft.WGapLink1.s4_wTilable
#print axioms Erdos634.Draft.WGapLink1.rwStatement_nsqW
