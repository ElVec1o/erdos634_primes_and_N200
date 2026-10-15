/-
Draft/RATrap2.lean -- the S5 leaf with the two-`c`-edges filter on the base.

`S5PinC.base_two_c`: in a dissection of the S5 target `(α+β, α+β, α)` the base carries at
least two `c`-edges.  So an instance `(t, e, f)` whose base `t e (f² − e²)` has no word `P·ef + Q·(f²−e²) + R·f²` with
`R ≥ 2` needs no certificate (`raStatement_of_inst_trap2`).

Parametric consequence (`s5word2_k`): for the family `(2, k, k+1)`, `k ≥ 1`, the base word is forced to `R = 1`
(`S5PinArith.base_word_k`), so EVERY instance `(2, k, k+1)` is excluded with no search.

Composite-N leaves.  No sorry, no native_decide.
-/
import Erdos634.Draft.RATrap
import Erdos634.Draft.S5PinC
import Erdos634.Draft.S5PinArith

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RAAssemble Erdos634.CertCoord

namespace Erdos634.Draft.NSQM

/-- a word of the base `t e (f²−e²)` with at least two `c`-edges -/
def S5Word2 (t e f : ℤ) : Prop :=
  ∃ P Q R : ℕ, 2 ≤ R ∧ t * e * (f ^ 2 - e ^ 2) = P * (e * f) + Q * (f ^ 2 - e ^ 2) + R * f ^ 2

theorem S5Word2.toWord {t e f : ℤ} (h : S5Word2 t e f) : S5Word t e f e := by
  obtain ⟨P, Q, R, hR, hw⟩ := h
  exact ⟨P, Q, R, by omega, hw⟩

/-- **The base of an S5 target carries at least two `c`-edges** (`S5PinC.base_two_c` in the vocabulary of `s5_words`). -/
theorem s5_base_two {N : ℕ} (hN : 0 < N) (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi) (hmod : D.model.ThreeAlphaData α β a b c)
    (hP0 : D.target.angleAt 0 = α + β) (hP1 : D.target.angleAt 1 = α + β)
    (hwa : ∀ x y z : ℕ, a = x * a + y * b + z * c → x + y + z = 1)
    (hwb : ∀ x y z : ℕ, b = x * a + y * b + z * c → x + y + z = 1) :
    ∃ P Q R : ℕ, 2 ≤ R ∧ D.target.oppLen 2 = P * a + Q * b + R * c := by
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hmod
  set D2 := D.relabelModel σm with hD2
  have hmp : ∀ k, D2.model.pts k = D.model.pts (σm k) := fun _ => rfl
  have ha0 : D2.model.angleAt 0 = α := (Row14AnyLabel.angleAt_of_pts σm hmp 0).trans hα0m
  have ha1 : D2.model.angleAt 1 = β := (Row14AnyLabel.angleAt_of_pts σm hmp 1).trans hβ1m
  have ha2 : D2.model.angleAt 2 = 2 * α + β := (Row14AnyLabel.angleAt_of_pts σm hmp 2).trans hγ2m
  have ho0 : D2.model.oppLen 0 = a := (Row14AnyLabel.oppLen_of_pts σm hmp 0).trans ham
  have ho1 : D2.model.oppLen 1 = b := (Row14AnyLabel.oppLen_of_pts σm hmp 1).trans hbm
  have ho2 : D2.model.oppLen 2 = c := (Row14AnyLabel.oppLen_of_pts σm hmp 2).trans hcm
  have hαpos : 0 < α := ha0 ▸ D2.model.angleAt_pos' 0
  have hβpos : 0 < β := ha1 ▸ D2.model.angleAt_pos' 1
  have hαβ : α ≠ β := fun h => hα ⟨1 / 5, by push_cast; linarith⟩
  have hαγ : α ≠ 2 * α + β := fun h => hα ⟨1, by push_cast; linarith⟩
  have hβγ : β ≠ 2 * α + β := fun h => hαpos.ne' (by linarith)
  have hne : ∀ m m' : Fin 3, m ≠ m' → D2.model.oppLen m ≠ D2.model.oppLen m' := by
    intro m m' hmm h
    have hang := Erdos634.Draft.ISUMain.angleAt_eq_of_oppLen_eq D2.model m m' hmm h
    have fin3 : ∀ x : Fin 3, x = 0 ∨ x = 1 ∨ x = 2 := by decide
    rcases fin3 m with rfl | rfl | rfl <;> rcases fin3 m' with rfl | rfl | rfl <;>
      first
      | exact absurd rfl hmm
      | (rw [ha0, ha1] at hang; exact hαβ hang)
      | (rw [ha0, ha2] at hang; exact hαγ hang)
      | (rw [ha1, ha0] at hang; exact hαβ hang.symm)
      | (rw [ha1, ha2] at hang; exact hβγ hang)
      | (rw [ha2, ha0] at hang; exact hαγ hang.symm)
      | (rw [ha2, ha1] at hang; exact hβγ hang.symm)
  have X : Erdos634.Draft.S5Pin.Ctx D2 α β (2 * α + β) a b c :=
    { hA := ⟨hαpos, hβpos, hαβ, rfl, hrel, hα⟩
      hs0 := ho0
      hs1 := ho1
      hs2 := ho2
      hab := by have := hne 0 1 (by decide); rwa [ho0, ho1] at this
      hac := by have := hne 0 2 (by decide); rwa [ho0, ho2] at this
      hbc := by have := hne 1 2 (by decide); rwa [ho1, ho2] at this
      hα' := ha0
      hβ' := ha1
      hγ' := ha2
      hwa := hwa
      hwb := hwb }
  exact Erdos634.Draft.S5Pin.base_two_c hN X 0 hP0 hP1

set_option maxHeartbeats 4000000 in
theorem raStatement_of_inst_trap2 (N : ℕ)
    (hinst : ∀ t e f : ℤ, 2 ≤ t → 0 < e → e < f → IsCoprime e f → (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) →
      S5Word2 t e f → S5Word t e f f → S5Inst t e f) :
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
      -- the γ-trap words of the base and of a leg
      obtain ⟨-, ⟨P', Q', R', hR', hleg⟩⟩ :=
        s5_words (by have := D.pos; omega) D' hα hrel ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ hP0 hP1
      -- `a` and `b` are not words of two or more tile sides (integers `p q`, `q² − p²`, `q²` after scaling)
      have hscale : ∀ x y z : ℕ, ((x : ℝ) * ((p_i : ℝ) * q_i) + (y : ℝ) * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2)
            + (z : ℝ) * (q_i : ℝ) ^ 2) * c
          = (q_i : ℝ) ^ 2 * ((x : ℝ) * a + (y : ℝ) * b + (z : ℝ) * c) := by
        intro x y z
        rw [ha_sc, hb_sc, hsr, hr_pq]; first | (field_simp; ring) | field_simp
      have hwa_r : ∀ x y z : ℕ, a = x * a + y * b + z * c → x + y + z = 1 := by
        intro x y z h
        apply Erdos634.Draft.S5PinArith.word_a_single hp_pos hp_lt_q hcop_pq x y z
        have e1 := hscale x y z
        rw [← h] at e1
        have e2 : (q_i : ℝ) ^ 2 * a = ((p_i : ℝ) * q_i) * c := by
          rw [ha_sc, hsr, hr_pq]; first | (field_simp; ring) | field_simp
        rw [e2] at e1
        have e3 := mul_right_cancel₀ hc.ne' e1
        exact_mod_cast e3
      have hwb_r : ∀ x y z : ℕ, b = x * a + y * b + z * c → x + y + z = 1 := by
        intro x y z h
        apply Erdos634.Draft.S5PinArith.word_b_single hp_pos hp_lt_q hcop_pq x y z
        have e1 := hscale x y z
        rw [← h] at e1
        have e2 : (q_i : ℝ) ^ 2 * b = ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) * c := by
          rw [hb_sc, hsr, hr_pq]; first | (field_simp; ring) | field_simp
        rw [e2] at e1
        have e3 := mul_right_cancel₀ hc.ne' e1
        exact_mod_cast e3
      obtain ⟨P, Q, R, hR, hbase⟩ := s5_base_two (by have := D.pos; omega) D' hα hrel
        ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ hP0 hP1 hwa_r hwb_r
      have hwb : S5Word2 t p_i q_i := by
        refine ⟨P, Q, R, hR, ?_⟩
        have e1 : ((t : ℝ) * p_i * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2)
              - ((P : ℝ) * ((p_i : ℝ) * q_i) + (Q : ℝ) * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) + (R : ℝ) * (q_i : ℝ) ^ 2)) * c
            = (q_i : ℝ) ^ 2 * ((p_i : ℝ) / q_i * ((t : ℝ) * c * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / q_i)
              - ((P : ℝ) * ((p_i : ℝ) / q_i * c) + (Q : ℝ) * ((1 - ((p_i : ℝ) / q_i) ^ 2) * c) + (R : ℝ) * c)) := by
          field_simp
        have e2 : (p_i : ℝ) / q_i * ((t : ℝ) * c * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / q_i)
            = (P : ℝ) * ((p_i : ℝ) / q_i * c) + (Q : ℝ) * ((1 - ((p_i : ℝ) / q_i) ^ 2) * c) + (R : ℝ) * c := by
          rw [← hX0, ← hr_pq, ← hsr, ← hO2, ← ha_sc, ← hb_sc]; exact hbase
        rw [e2, sub_self, mul_zero] at e1
        have e3 := (mul_eq_zero.mp e1).resolve_right hc.ne'
        have e4 : (t : ℝ) * p_i * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2)
            = (P : ℝ) * ((p_i : ℝ) * q_i) + (Q : ℝ) * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) + (R : ℝ) * (q_i : ℝ) ^ 2 := by
          linarith
        exact_mod_cast e4
      have hwl : S5Word t p_i q_i q_i := by
        refine ⟨P', Q', R', hR', ?_⟩
        have e1 : ((t : ℝ) * q_i * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2)
              - ((P' : ℝ) * ((p_i : ℝ) * q_i) + (Q' : ℝ) * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) + (R' : ℝ) * (q_i : ℝ) ^ 2)) * c
            = (q_i : ℝ) ^ 2 * ((t : ℝ) * c * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / q_i
              - ((P' : ℝ) * ((p_i : ℝ) / q_i * c) + (Q' : ℝ) * ((1 - ((p_i : ℝ) / q_i) ^ 2) * c) + (R' : ℝ) * c)) := by
          field_simp
        have e2 : (t : ℝ) * c * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / q_i
            = (P' : ℝ) * ((p_i : ℝ) / q_i * c) + (Q' : ℝ) * ((1 - ((p_i : ℝ) / q_i) ^ 2) * c) + (R' : ℝ) * c := by
          rw [← hX0, ← hr_pq, ← hsr, ← ha_sc, ← hb_sc]; exact hleg
        rw [e2, sub_self, mul_zero] at e1
        have e3 := (mul_eq_zero.mp e1).resolve_right hc.ne'
        have e4 : (t : ℝ) * q_i * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2)
            = (P' : ℝ) * ((p_i : ℝ) * q_i) + (Q' : ℝ) * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) + (R' : ℝ) * (q_i : ℝ) ^ 2 := by
          linarith
        exact_mod_cast e4
      refine hinst t p_i q_i ht2 hp_pos hp_lt_q hcop_pq hNt hwb hwl Ds ?_ ?_ ?_ ⟨σm, ?_, ?_, ?_⟩
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

/-- **Parametric kill of the family `(2, k, k+1)`**: its base has no word with two `c`-edges. -/
theorem s5word2_k {k : ℤ} (hk : 1 ≤ k) : ¬ S5Word2 2 k (k + 1) := by
  rintro ⟨P, Q, R, hR, h⟩
  have := Erdos634.Draft.S5PinArith.base_word_k hk P Q R (by omega) h
  omega

/-- the instance `(3, 1, 2)`: base `9 = 2P + 3Q + 4R` has no solution with `R ≥ 2` -/
theorem s5word2_3_1_2 : ¬ S5Word2 3 1 2 := by
  rintro ⟨P, Q, R, hR, h⟩
  have h' : (9 : ℤ) = 2 * P + 3 * Q + 4 * R := by
    have : (3 : ℤ) * 1 * (2 ^ 2 - 1 ^ 2) = P * (1 * 2) + Q * (2 ^ 2 - 1 ^ 2) + R * 2 ^ 2 := h
    linarith
  omega

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.s5_base_two
#print axioms Erdos634.Draft.NSQM.raStatement_of_inst_trap2
#print axioms Erdos634.Draft.NSQM.s5word2_k
