/-
Draft/B3Prime.lean -- `prop:b3prime`: no isosceles triangle with base angles `α + β` (`3α + 2β = π`, `α/π` irrational)
has a dissection into a PRIME number of congruent tiles with angles `(α, β, 2α + β)`.

Route (independent of `TheoremP6` and of `not_baseBetaTiled`):
* `s5_shape`: any dissection of that target has the atom shape -- there are integers `t ≥ 1`, coprime `0 < e < f` with
  `N = t² (f² − e²)` (from `NSQM.setupM`: area and boundary parity, and `RAInst.km_shape`), and the base and a leg
  carry a `c`-edge: the words `S5Word t e f e`, `S5Word t e f f` (γ-trap, `RATrap.s5_words`).  This is the first half
  of `RATrap.raStatement_of_inst_trap`, with the rationality of `a / c` DERIVED (`s = (K² − N)/(K² + N)`) instead of
  assumed.  Only the γ-trap is used (not the two-`c`-edges theorem of `S5PinC`).
* `N` prime forces `t = 1`, `f = e + 1`, and `s5word_1_k`: the base `k (2k+1)` of the instance `(1, k, k+1)` has no
  word with a `c`-edge.

Paper label `prop:b3prime` (main paper).  NOT prime-case progress in the sense of outcome (2): the target here is the
isosceles `(α+β, α+β, α)` triangle, one branch of the classification, and the statement concerns every prime `N`.
No sorry, no native_decide.
-/
import Erdos634.Draft.RATrap

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord Erdos634.Realizable
  Erdos634.Draft.TheoremPConditional Erdos634.Draft.RAAssemble Erdos634.CertCoord

namespace Erdos634.Draft.NSQM

set_option maxHeartbeats 4000000 in
/-- **The atom shape of a dissected `(α+β, α+β, α)` target**, with the γ-trap words. -/
theorem s5_shape {N : ℕ} (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi) (hmod : D.model.ThreeAlphaData α β a b c)
    (htgt : TgtAngles D (α + β) (α + β) α) :
    ∃ t e f : ℤ, 0 < t ∧ 0 < e ∧ e < f ∧ IsCoprime e f ∧ (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) ∧
      S5Word t e f e ∧ S5Word t e f f := by
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
  -- rationality of `s = a / c`, from the area relation `N (1 + s) = K² (1 - s)`
  have hN0R : (0 : ℝ) < (N : ℝ) := by
    have := D.pos
    exact_mod_cast this
  have hden : (0 : ℝ) < (K : ℝ) ^ 2 + N := by positivity
  set r : ℚ := ((K : ℚ) ^ 2 - N) / ((K : ℚ) ^ 2 + N) with hrdef
  have hsr : s = (r : ℝ) := by
    rw [hrdef]; push_cast
    rw [eq_div_iff hden.ne']
    linarith
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
  obtain ⟨t, ht0, hKt, hMt, hNt⟩ := km_shape hp_pos hp_lt_q hcop_pq hKpos hMpos hNKM hKp hMp hrelKM
  obtain ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ := hmod
  have hKR : (K : ℝ) = ((q_i : ℝ) + p_i) * t := by exact_mod_cast hKt
  have hX0 : D'.target.oppLen 0 = (t : ℝ) * c * ((q_i : ℝ) ^ 2 - (p_i : ℝ) ^ 2) / q_i := by
    rw [← hKc, hsr, hr_pq, hKR]; first | (field_simp; ring) | field_simp
  -- the γ-trap words of the base and of a leg
  obtain ⟨⟨P, Q, R, hR, hbase⟩, ⟨P', Q', R', hR', hleg⟩⟩ :=
    s5_words (by have := D.pos; omega) D' hα hrel ⟨σm, hα0m, ham, hβ1m, hbm, hγ2m, hcm⟩ hP0 hP1
  have hwb : S5Word t p_i q_i p_i := by
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
  exact ⟨t, p_i, q_i, ht0, hp_pos, hp_lt_q, hcop_pq, hNt, hwb, hwl⟩

/-- the base `k (2k+1)` of the instance `(1, k, k+1)` has no word with a `c`-edge -/
theorem s5word_1_k {k : ℤ} (hk : 1 ≤ k) : ¬ S5Word 1 k (k + 1) k := by
  rintro ⟨P, Q, R, hR, h⟩
  have hP0 : (0 : ℤ) ≤ (P : ℤ) := Int.natCast_nonneg _
  have hQ0 : (0 : ℤ) ≤ (Q : ℤ) := Int.natCast_nonneg _
  have hR1 : (1 : ℤ) ≤ (R : ℤ) := by exact_mod_cast hR
  have hb : (k + 1) ^ 2 - k ^ 2 = 2 * k + 1 := by ring
  rw [hb] at h
  -- `(R − P)(k+1)² ≡ 0 (mod 2k+1)` and `(k+1)²` is a unit there
  have hdvd : (2 * k + 1) ∣ ((R : ℤ) - P) := by
    have h1 : (2 * k + 1) ∣ ((R : ℤ) - P) * (k + 1) ^ 2 :=
      ⟨k - Q - P * (k + 1), by linear_combination -h⟩
    have hc : IsCoprime (2 * k + 1) ((k + 1) ^ 2) := by
      have : IsCoprime (2 * k + 1) (k + 1) := ⟨-1, 2, by ring⟩
      exact this.pow_right
    exact hc.dvd_of_dvd_mul_right h1
  obtain ⟨m, hm⟩ := hdvd
  have hk0 : 0 < k := by linarith
  rcases lt_trichotomy m 0 with hneg | hzero | hpos
  · have hP : (P : ℤ) ≥ R + (2 * k + 1) := by nlinarith
    nlinarith [mul_nonneg hQ0 (by linarith : (0 : ℤ) ≤ 2 * k + 1),
      mul_nonneg (by linarith : (0 : ℤ) ≤ (R : ℤ)) (by positivity : (0 : ℤ) ≤ (k + 1) ^ 2),
      mul_le_mul_of_nonneg_right hP (by nlinarith : (0 : ℤ) ≤ k * (k + 1))]
  · -- `R = P`: `P (k+1) + Q = k` forces `P = 0`
    have hRP : (R : ℤ) = P := by rw [hzero] at hm; linarith
    rw [hRP] at h hR1
    have h2 : (P : ℤ) * (k + 1) + Q = k := by
      have h3 : ((P : ℤ) * (k + 1) + Q - k) * (2 * k + 1) = 0 := by linear_combination -h
      have hne : (2 * k + 1) ≠ 0 := by linarith
      have := (mul_eq_zero.mp h3).resolve_right hne
      linarith
    nlinarith
  · have hRge : (R : ℤ) ≥ 2 * k + 1 := by nlinarith
    nlinarith [mul_nonneg hQ0 (by linarith : (0 : ℤ) ≤ 2 * k + 1),
      mul_nonneg hP0 (by nlinarith : (0 : ℤ) ≤ k * (k + 1)),
      mul_le_mul_of_nonneg_right hRge (by positivity : (0 : ℤ) ≤ (k + 1) ^ 2)]

/-- **`prop:b3prime`.**  No triangle with angles `(α+β, α+β, α)` has a dissection into a prime number of congruent
triangles with angles `(α, β, 2α+β)`, where `3α + 2β = π` and `α/π` is irrational. -/
theorem b3prime {N : ℕ} (hN : N.Prime) (D : CongruentDissection N) {α β a b c : ℝ}
    (hα : IrrPi α) (hrel : 3 * α + 2 * β = Real.pi) (hmod : D.model.ThreeAlphaData α β a b c)
    (htgt : TgtAngles D (α + β) (α + β) α) : False := by
  obtain ⟨t, e, f, ht, he, hef, hcop, hNt, hwb, -⟩ := s5_shape D hα hrel hmod htgt
  -- `N = t · (t (f² − e²))` prime, `f² − e² ≥ 3`: `t = 1`
  have hb3 : 3 ≤ f ^ 2 - e ^ 2 := by nlinarith
  have ht1 : t = 1 := by
    by_contra hne
    have ht2 : 2 ≤ t := by omega
    have hdvd : (t.toNat : ℕ) ∣ N := by
      have h1 : (t : ℤ) ∣ (N : ℤ) := ⟨t * (f ^ 2 - e ^ 2), by rw [hNt]; ring⟩
      have h2 : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
      rw [← h2] at h1
      exact_mod_cast h1
    rcases (Nat.dvd_prime hN).mp hdvd with h1 | h1
    · have : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
      rw [h1] at this; omega
    · have h2 : ((t.toNat : ℕ) : ℤ) = t := Int.toNat_of_nonneg (by omega)
      rw [h1] at h2
      rw [← h2] at hNt ht2
      nlinarith
  subst ht1
  -- `N = (f − e)(f + e)` prime: `f = e + 1`
  have hfe : f = e + 1 := by
    by_contra hne
    have hd2 : 2 ≤ f - e := by omega
    have hdvd : ((f - e).toNat : ℕ) ∣ N := by
      have h1 : (f - e : ℤ) ∣ (N : ℤ) := ⟨f + e, by rw [hNt]; ring⟩
      have h2 : (((f - e).toNat : ℕ) : ℤ) = f - e := Int.toNat_of_nonneg (by omega)
      rw [← h2] at h1
      exact_mod_cast h1
    rcases (Nat.dvd_prime hN).mp hdvd with h1 | h1
    · have : (((f - e).toNat : ℕ) : ℤ) = f - e := Int.toNat_of_nonneg (by omega)
      rw [h1] at this; omega
    · have h2 : (((f - e).toNat : ℕ) : ℤ) = f - e := Int.toNat_of_nonneg (by omega)
      rw [h1] at h2
      have : (N : ℤ) = (f - e) * (f + e) := by rw [hNt]; ring
      rw [← h2] at this
      have hN0 : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN.pos
      nlinarith
  subst hfe
  exact s5word_1_k (by omega) hwb

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.s5_shape
#print axioms Erdos634.Draft.NSQM.b3prime
