-- Draft/SIXIso33.lean
-- `GapIsoSporadic33` reduction: a copy of `ThmIsoH9b` (thm:iso, 2π/3 tile, isosceles base-α target) in which the
-- leaf `IsoH9b N` is NOT assumed.  Instead, at N = 33 the surviving proper-divisor candidate is shown to be the
-- primitive triple (a,b,c) = (5,3,7) with μ = 3, i.e. (after rescaling) the model has sides (5,3,7) and the
-- target (21,21,33).  The remaining geometric fact (that this instance admits no dissection) is the certified
-- search of `SIXBridgeIso33`.
import Erdos634.Draft.ThmIsoH9b
import Erdos634.Draft.SIXS21Reduce

open scoped Classical

namespace Erdos634.Draft.SIXIso33

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

/-- The only 120° candidate at `N = 33`: `(a,b,c,k) = (5,3,7,3)`. -/
theorem sporadic33 (a b c k : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hk : 0 < k)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2) (h3 : 3 ≤ a + 2 * b) (hdvd : (a + 2 * b) ∣ (33 : ℤ))
    (hne : a + 2 * b ≠ 33) (harea : b * 33 = k ^ 2 * (a + 2 * b)) :
    a = 5 ∧ b = 3 ∧ c = 7 ∧ k = 3 := by
  obtain ⟨e, he⟩ : ∃ e : ℤ, e = a + 2 * b := ⟨_, rfl⟩
  rw [← he] at hdvd hne h3 harea
  have hle : e ≤ 33 := Int.le_of_dvd (by norm_num) hdvd
  have hcases : e = 3 ∨ e = 11 := by interval_cases e <;> omega
  rcases hcases with h | h
  · exfalso
    have h1 : a = 1 := by omega
    have h2 : b = 1 := by omega
    subst h1; subst h2
    have : c ≤ 2 := by nlinarith
    interval_cases c <;> omega
  · have hb5 : b ≤ 5 := by omega
    have ha_ : a = 11 - 2 * b := by omega
    subst ha_
    have hc10 : c ≤ 10 := by nlinarith
    rw [h] at harea
    interval_cases b <;> interval_cases c <;> first | (exfalso; norm_num at hc2; done) | skip
    have hk3 : k ≤ 3 := by nlinarith
    interval_cases k <;> first | omega | (exact ⟨by norm_num, rfl, rfl, rfl⟩)

private lemma twoPiThreeData_swap {T : Tri} {α a b c : ℝ}
    (h : T.TwoPiThreeData α a b c) :
    T.TwoPiThreeData (Real.pi / 3 - α) b a c := by
  obtain ⟨σ, h0, ha, h1, hb, h2, hc⟩ := h
  refine ⟨σ * Equiv.swap 0 1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact h1
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_left]; exact hb
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; rw [h0]; ring
  · simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_right]; exact ha
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact h2
  · simp only [Equiv.Perm.mul_apply]
    have : Equiv.swap (0 : Fin 3) 1 2 = 2 := by decide
    rw [this]; exact hc

private lemma irrPi_beta {α : ℝ} (h : IrrPi α) : IrrPi (Real.pi / 3 - α) :=
  fun ⟨r, hr⟩ => h ⟨1 / 3 - r, by push_cast at hr ⊢; linarith⟩

-- r²=q²+q+1 forces q.den = r.den
private lemma rat_den_eq (q r : ℚ) (heq : r ^ 2 = q ^ 2 + q + 1) : q.den = r.den := by
  have hqd_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
  have hrd_ne : (r.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr r.pos.ne'
  -- Clear denominators to get integer equation
  have hint : (r.num : ℤ) ^ 2 * (q.den : ℤ) ^ 2 =
      ((q.num : ℤ) ^ 2 + q.num * q.den + (q.den : ℤ) ^ 2) * (r.den : ℤ) ^ 2 := by
    have hq : (q : ℚ) = q.num / q.den := q.num_div_den.symm
    have hr : (r : ℚ) = r.num / r.den := r.num_div_den.symm
    have key := heq
    rw [hq, hr] at key
    have h : (r.num : ℚ) ^ 2 * q.den ^ 2 =
        (q.num ^ 2 + q.num * q.den + q.den ^ 2) * r.den ^ 2 := by
      field_simp [hqd_ne, hrd_ne] at key ⊢
      linarith
    exact_mod_cast h
  -- r.den | q.den
  have hrd_dvd : r.den ∣ q.den := by
    have hdvd : (r.den : ℤ) ^ 2 ∣ (r.num : ℤ) ^ 2 * (q.den : ℤ) ^ 2 :=
      ⟨(q.num : ℤ)^2 + q.num * q.den + (q.den : ℤ)^2, by linear_combination hint⟩
    have hrcop2 : IsCoprime ((r.den : ℤ) ^ 2) ((r.num : ℤ) ^ 2) :=
      (Rat.isCoprime_num_den r).symm.pow_left.pow_right
    have h2 : (r.den : ℤ) ^ 2 ∣ (q.den : ℤ) ^ 2 :=
      hrcop2.dvd_of_dvd_mul_left hdvd
    exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp (by exact_mod_cast h2)
  -- q.den | r.den
  have hqd_dvd : q.den ∣ r.den := by
    have hdvd2 : (q.den : ℤ) ^ 2 ∣
        ((q.num : ℤ) ^ 2 + q.num * q.den + (q.den : ℤ) ^ 2) * (r.den : ℤ) ^ 2 :=
      ⟨(r.num : ℤ) ^ 2, by linear_combination -hint⟩
    have hcop : IsCoprime (q.den : ℤ) ((q.num : ℤ) ^ 2 + q.num * q.den + (q.den : ℤ) ^ 2) := by
      have h : IsCoprime (q.den : ℤ) ((q.num : ℤ) ^ 2) :=
        (Rat.isCoprime_num_den q).symm.pow_right
      have h2 : IsCoprime (q.den : ℤ) ((q.num : ℤ) ^ 2 + (q.den : ℤ) * (q.num + q.den)) :=
        h.add_mul_left_right _
      rwa [show (q.num : ℤ) ^ 2 + (q.den : ℤ) * (q.num + q.den) =
               q.num ^ 2 + q.num * q.den + q.den ^ 2 from by ring] at h2
    have h2 : (q.den : ℤ) ^ 2 ∣ (r.den : ℤ) ^ 2 :=
      hcop.pow_left.dvd_of_dvd_mul_left hdvd2
    exact (Nat.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp (by exact_mod_cast h2)
  exact (Nat.dvd_antisymm hrd_dvd hqd_dvd).symm

set_option maxHeartbeats 800000 in
private lemma thmIso_arith_bridge_b
    (N : ℕ) (hN33 : N = 33)
    (a b c μ : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hμ : 0 < μ)
    (hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (harea : (N : ℝ) * b = μ ^ 2 * (a + 2 * b))
    (nA nB : ℤ)
    (hA : (nA : ℝ) = (μ / b) * (c - a - b))
    (hB : (nB : ℝ) = (μ / b) * (c + a + b)) (hpA : (2 : ℤ) ∣ nA - N) :
    a * 3 = 5 * b ∧ c * 3 = 7 * b ∧ μ = 3 := by
  have hP_ne : μ / b ≠ 0 := (div_pos hμ hb).ne'
  -- tile_rational: get q, r : ℚ with a = q*b, c = r*b
  obtain ⟨q, r, haq, hcr⟩ :=
    Erdos634.Rationality.tile_rational a b c (μ/b) hc2 hb.ne' hP_ne (by positivity) N nA nB
      (by push_cast; field_simp [hb.ne']; linarith [harea])
      (by push_cast; linarith [hA])
      (by push_cast; linarith [hB])
  -- r² = q² + q + 1 over ℚ
  have hrq_sq : r ^ 2 = q ^ 2 + q + 1 := by
    have hb2 : (b : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hb.ne'
    have key : ((r : ℝ) ^ 2 - ((q : ℝ) ^ 2 + q + 1)) * b ^ 2 = 0 := by
      push_cast [haq, hcr] at hc2 ⊢; nlinarith
    have := (mul_eq_zero.mp key).resolve_right hb2
    exact_mod_cast sub_eq_zero.mp this
  -- Denominators agree
  have hden_eq : q.den = r.den := rat_den_eq q r hrq_sq
  -- Integer triple
  set a₀ : ℤ := q.num
  set b₀ : ℤ := (q.den : ℤ)
  set c₀ : ℤ := r.num
  have hb0_pos : 0 < b₀ := by simp only [b₀]; exact_mod_cast q.pos
  have ha0_pos : 0 < a₀ := by
    have hq_pos : 0 < (q : ℚ) := by
      have : 0 < (q : ℝ) := by
        have hqb : (q : ℝ) * b = a := haq.symm
        exact (mul_pos_iff.mp (show 0 < q * b by rw [hqb]; exact ha)).resolve_right
          (fun ⟨_, hh⟩ => absurd hh (not_lt.mpr hb.le)) |>.1
      exact_mod_cast this
    exact_mod_cast Rat.num_pos.mpr hq_pos
  have hc0_pos : 0 < c₀ := by
    have hr_pos : 0 < (r : ℚ) := by
      have : 0 < (r : ℝ) := by
        have hrb : (r : ℝ) * b = c := hcr.symm
        exact (mul_pos_iff.mp (show 0 < r * b by rw [hrb]; exact hc)).resolve_right
          (fun ⟨_, hh⟩ => absurd hh (not_lt.mpr hb.le)) |>.1
      exact_mod_cast this
    exact_mod_cast Rat.num_pos.mpr hr_pos
  -- c₀² = a₀² + a₀*b₀ + b₀²  in ℤ
  have hc0_sq : c₀ ^ 2 = a₀ ^ 2 + a₀ * b₀ + b₀ ^ 2 := by
    have hqd_ne : (q.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr q.pos.ne'
    have h_rat : (r.num : ℚ) ^ 2 =
        (q.num : ℚ) ^ 2 + (q.num : ℚ) * q.den + (q.den : ℚ) ^ 2 := by
      have h := hrq_sq
      rw [show (q : ℚ) = q.num / q.den from q.num_div_den.symm,
          show (r : ℚ) = r.num / r.den from r.num_div_den.symm, ← hden_eq] at h
      field_simp [hqd_ne] at h
      linarith
    exact_mod_cast h_rat
  have hcop_ab : IsCoprime a₀ b₀ := Rat.isCoprime_num_den q
  have hcop_b_a2b : IsCoprime b₀ (a₀ + 2 * b₀) := hcop_ab.symm.add_mul_right_right 2
  -- IsCoprime a₀ c₀
  have hcop_ac : IsCoprime a₀ c₀ := by
    -- c₀² = b₀² + a₀*(a₀+b₀), so IsCoprime a₀ (b₀²) → IsCoprime a₀ (c₀²) → IsCoprime a₀ c₀
    rw [← IsCoprime.pow_right_iff (by norm_num : 0 < 2)]
    rw [show c₀ ^ 2 = b₀ ^ 2 + a₀ * (a₀ + b₀) from by linarith [hc0_sq]]
    exact hcop_ab.pow_right.add_mul_left_right (a₀ + b₀)
  -- Auxiliary
  have hb0_r : (b₀ : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hb0_pos.ne'
  -- q * q.den = q.num and r * q.den = r.num (over ℝ), used multiple times
  have hqnd : (q : ℝ) * q.den = q.num := by
    have : (q : ℚ) * q.den = q.num := by
      nth_rw 1 [q.num_div_den.symm]; field_simp [Nat.cast_ne_zero.mpr q.pos.ne']
    exact_mod_cast this
  have hrnd : (r : ℝ) * q.den = r.num := by
    have h : (r : ℝ) * r.den = r.num := by
      have : (r : ℚ) * r.den = r.num := by
        nth_rw 1 [r.num_div_den.symm]; field_simp [Nat.cast_ne_zero.mpr r.pos.ne']
      exact_mod_cast this
    have hd : (q.den : ℝ) = r.den := by exact_mod_cast hden_eq
    rw [← hd] at h; exact h
  -- μ * (c₀ - a₀ - b₀) = nA * b₀  as reals
  have hcab_real : μ * ((c₀ - a₀ - b₀ : ℤ) : ℝ) = ((nA * b₀ : ℤ) : ℝ) := by
    push_cast
    have hAb : (nA : ℝ) * b = μ * (c - a - b) := by rw [hA]; field_simp [hb.ne']
    have h1 : μ * ((r.num : ℝ) - q.num - q.den) * b = μ * (c - a - b) * q.den := by
      rw [hcr, haq, ← hrnd, ← hqnd]; ring
    apply mul_right_cancel₀ hb.ne'
    linear_combination h1 - (q.den : ℝ) * hAb
  -- μ * (c₀ + a₀ + b₀) = nB * b₀  as reals
  have hcab2_real : μ * ((c₀ + a₀ + b₀ : ℤ) : ℝ) = ((nB * b₀ : ℤ) : ℝ) := by
    push_cast
    have hBb : (nB : ℝ) * b = μ * (c + a + b) := by rw [hB]; field_simp [hb.ne']
    have h1 : μ * ((r.num : ℝ) + q.num + q.den) * b = μ * (c + a + b) * q.den := by
      rw [hcr, haq, ← hrnd, ← hqnd]; ring
    apply mul_right_cancel₀ hb.ne'
    linear_combination h1 - (q.den : ℝ) * hBb
  -- a = (a₀/b₀)*b, used in harea_int and harea_sc below
  have ha_eq : (a : ℝ) = a₀ / b₀ * b := by
    simp only [a₀, b₀]; push_cast
    rw [← show (q : ℝ) = q.num / q.den from by exact_mod_cast q.num_div_den.symm]
    exact haq
  -- Get integer k with μ = k via 2*μ² = N + nA*nB ∈ ℤ
  have hd_ne : (c₀ - a₀ - b₀ : ℤ) ≠ 0 := by
    intro h0
    have hcab0_zero := hcab_real
    rw [show ((c₀ - a₀ - b₀ : ℤ) : ℝ) = 0 from by exact_mod_cast h0, mul_zero] at hcab0_zero
    have hnA : nA = 0 := by
      have : (nA * b₀ : ℤ) = 0 := by exact_mod_cast hcab0_zero.symm
      exact (mul_eq_zero.mp this).resolve_right hb0_pos.ne'
    have hcab0 : c = a + b := by
      have hnA_r : (nA : ℝ) = 0 := by exact_mod_cast hnA
      have hmcab : (μ / b) * (c - a - b) = 0 := by linarith [hA, hnA_r]
      rcases mul_eq_zero.mp hmcab with h | h
      · exact absurd h hP_ne
      · linarith
    have hc2' := hc2; rw [hcab0] at hc2'
    nlinarith [hc2', mul_pos ha hb]
  let qμ : ℚ := (nA * b₀ : ℤ) / ((c₀ - a₀ - b₀ : ℤ) : ℚ)
  have hqmu_eq : μ = qμ := by
    have hd_r : ((c₀ - a₀ - b₀ : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hd_ne
    rw [show (qμ : ℝ) = ((nA * b₀ : ℤ) : ℝ) / ((c₀ - a₀ - b₀ : ℤ) : ℝ) from by simp [qμ]]
    rw [eq_comm, div_eq_iff hd_r]
    linarith [hcab_real]
  have h2mu2 : 2 * μ ^ 2 = (N : ℝ) + nA * nB := by
    have hprod : μ ^ 2 * ((c₀ - a₀ - b₀ : ℤ) : ℝ) * ((c₀ + a₀ + b₀ : ℤ) : ℝ) =
        (nA : ℝ) * nB * (b₀ : ℝ) ^ 2 := by
      have h1 : μ * ((c₀ - a₀ - b₀ : ℤ) : ℝ) = (nA : ℝ) * b₀ := by
        have := hcab_real; push_cast at this ⊢; linarith
      have h2 : μ * ((c₀ + a₀ + b₀ : ℤ) : ℝ) = (nB : ℝ) * b₀ := by
        have := hcab2_real; push_cast at this ⊢; linarith
      calc μ ^ 2 * ((c₀ - a₀ - b₀ : ℤ) : ℝ) * ((c₀ + a₀ + b₀ : ℤ) : ℝ)
          = μ * ((c₀ - a₀ - b₀ : ℤ) : ℝ) * (μ * ((c₀ + a₀ + b₀ : ℤ) : ℝ)) := by ring
        _ = (nA : ℝ) * b₀ * ((nB : ℝ) * b₀) := by rw [h1, h2]
        _ = nA * nB * b₀ ^ 2 := by ring
    have hident : ((c₀ - a₀ - b₀ : ℤ) : ℝ) * ((c₀ + a₀ + b₀ : ℤ) : ℝ) =
        -(a₀ : ℝ) * b₀ := by
      have hc0_sq_r : ((c₀ : ℤ) : ℝ) ^ 2 = (a₀ : ℝ) ^ 2 + (a₀ : ℝ) * b₀ + (b₀ : ℝ) ^ 2 :=
        by exact_mod_cast hc0_sq
      push_cast; nlinarith [hc0_sq_r]
    have hprod_fac : μ ^ 2 * (-(a₀ : ℝ) * b₀) = (nA : ℝ) * nB * b₀ ^ 2 :=
      calc μ ^ 2 * (-(a₀ : ℝ) * b₀)
          = μ ^ 2 * (((c₀-a₀-b₀:ℤ):ℝ) * ((c₀+a₀+b₀:ℤ):ℝ)) := by rw [hident]
        _ = μ ^ 2 * ((c₀-a₀-b₀:ℤ):ℝ) * ((c₀+a₀+b₀:ℤ):ℝ) := by ring
        _ = (nA : ℝ) * nB * b₀ ^ 2 := hprod
    have harea_sc : μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) = (N : ℝ) * b₀ := by
      apply mul_right_cancel₀ hb.ne'
      calc μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) * b
          = μ ^ 2 * (a₀ / b₀ * b + 2 * b) * b₀ := by field_simp [hb0_r]
        _ = μ ^ 2 * (a + 2 * b) * b₀ := by rw [ha_eq]
        _ = N * b * b₀ := by rw [harea]
        _ = N * b₀ * b := by ring
    have h2b : 2 * μ ^ 2 * b₀ ^ 2 = ((N : ℝ) + nA * nB) * b₀ ^ 2 := by
      -- key: μ²*(a₀+2b₀)*b₀ = N*b₀² (from harea_sc, multiplied by b₀)
      have key : μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) * b₀ = (N : ℝ) * b₀ ^ 2 := by
        rw [show μ ^ 2 * ((a₀ : ℝ) + 2 * b₀) * b₀ =
              (μ ^ 2 * ((a₀ : ℝ) + 2 * b₀)) * b₀ from by ring, harea_sc]; ring
      -- expand key: μ²*a₀*b₀ + 2*μ²*b₀² = N*b₀²
      have h1 : μ ^ 2 * (a₀ : ℝ) * b₀ + 2 * μ ^ 2 * b₀ ^ 2 = (N : ℝ) * b₀ ^ 2 := by
        linarith [show μ^2*((a₀:ℝ)+2*b₀)*b₀ = μ^2*(a₀:ℝ)*b₀ + 2*μ^2*b₀^2 from by ring, key]
      -- hprod_fac gives: μ²*a₀*b₀ = -nA*nB*b₀²
      have h2 : μ ^ 2 * (a₀ : ℝ) * b₀ = -((nA : ℝ) * nB * b₀ ^ 2) := by
        linarith [show μ^2*(-(a₀:ℝ)*b₀) = -(μ^2*(a₀:ℝ)*b₀) from by ring, hprod_fac]
      linarith [h1, h2]
    exact mul_right_cancel₀ (pow_ne_zero 2 hb0_r) (by linarith [h2b])
  have hden1 : qμ.den = 1 := by
    have h2q2 : 2 * qμ ^ 2 = ((N : ℤ) + nA * nB : ℤ) := by
      have : (2 * qμ ^ 2 : ℝ) = (((N : ℤ) + nA * nB : ℤ) : ℝ) := by
        push_cast; rw [← hqmu_eq]; linarith [h2mu2]
      exact_mod_cast this
    have hd_ne' : (qμ.den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr qμ.pos.ne'
    have hint_int : 2 * (qμ.num : ℤ) ^ 2 = (qμ.den : ℤ) ^ 2 * ((N : ℤ) + nA * nB) := by
      have h2q2' := h2q2
      rw [show (qμ : ℚ) = (qμ.num : ℚ) / qμ.den from qμ.num_div_den.symm] at h2q2'
      field_simp [hd_ne'] at h2q2'
      exact_mod_cast h2q2'
    have hdvd : (qμ.den : ℤ) ^ 2 ∣ 2 * qμ.num ^ 2 := by
      rw [hint_int]; exact dvd_mul_right _ _
    have hcop_pow : IsCoprime ((qμ.den : ℤ) ^ 2) ((qμ.num : ℤ) ^ 2) :=
      (Rat.isCoprime_num_den qμ).symm.pow_left.pow_right
    have hdvd2 : (qμ.den : ℤ) ^ 2 ∣ 2 :=
      hcop_pow.dvd_of_dvd_mul_left (by rwa [mul_comm] at hdvd)
    have hd_le : (qμ.den : ℤ) ^ 2 ≤ 2 := Int.le_of_dvd (by norm_num) hdvd2
    have hd_le1 : qμ.den ≤ 1 := by
      have hd_int : (0 : ℤ) < qμ.den := by exact_mod_cast qμ.pos
      have : (qμ.den : ℤ) ≤ 1 := by nlinarith [sq_nonneg ((qμ.den : ℤ) - 1), hd_le]
      exact_mod_cast this
    exact Nat.le_antisymm hd_le1 qμ.pos
  obtain ⟨k, hk⟩ : ∃ k : ℤ, μ = k :=
    ⟨qμ.num, by
      rw [hqmu_eq]
      have hqnum_eq : (qμ.num : ℚ) = qμ := by
        nth_rw 2 [← qμ.num_div_den]; rw [hden1, Nat.cast_one, div_one]
      exact_mod_cast hqnum_eq.symm⟩
  have hk_pos : 0 < k := by exact_mod_cast (show (0 : ℝ) < k by rw [← hk]; exact hμ)
  -- Area identity b₀*N = k²*(a₀+2*b₀) in ℤ
  have harea_int : b₀ * (N : ℤ) = k ^ 2 * (a₀ + 2 * b₀) := by
    have h_r : (b₀ : ℝ) * N = k ^ 2 * (a₀ + 2 * b₀) := by
      rw [hk] at harea
      apply mul_right_cancel₀ hb.ne'
      calc (b₀ : ℝ) * N * b
          = N * b * b₀ := by ring
        _ = k ^ 2 * (a + 2 * b) * b₀ := by rw [harea]
        _ = k ^ 2 * (a₀ / b₀ * b + 2 * b) * b₀ := by rw [ha_eq]
        _ = k ^ 2 * (a₀ + 2 * b₀) * b := by field_simp [hb0_r]
    exact_mod_cast h_r
  have ha2b_ge3 : 3 ≤ a₀ + 2 * b₀ := by linarith [ha0_pos, hb0_pos]
  have hdvd_e : (a₀ + 2 * b₀) ∣ (N : ℤ) :=
    hcop_b_a2b.symm.dvd_of_dvd_mul_left ⟨k ^ 2, by linarith [harea_int]⟩
  by_cases hNe : a₀ + 2 * b₀ = (N : ℤ)
  · have hksq : k ^ 2 = b₀ := by
      have hNpos : (N : ℤ) ≠ 0 := by rw [← hNe]; omega
      have hcancel : b₀ * (N : ℤ) = k ^ 2 * (N : ℤ) := by rw [harea_int, hNe]
      exact (mul_right_cancel₀ hNpos hcancel).symm
    have hkM : k * nA = c₀ - a₀ - b₀ := by
      have h_int : k * (c₀ - a₀ - b₀) = nA * k ^ 2 := by
        have h_real : (k : ℝ) * ((c₀ - a₀ - b₀ : ℤ) : ℝ) = ((nA * b₀ : ℤ) : ℝ) := by
          rw [← hk]; exact hcab_real
        have this_int := by exact_mod_cast h_real
        linear_combination this_int - nA * hksq
      exact Int.eq_of_mul_eq_mul_left hk_pos.ne' (by linear_combination -h_int)
    exact (iso_arith_core_H9b a₀ b₀ c₀ k nA ha0_pos hb0_pos hc0_pos hk_pos hc0_sq hcop_ac hksq hcop_b_a2b hkM).elim
  · have h_int : k * (c₀ - a₀ - b₀) = nA * b₀ := by
      have h_real : (k : ℝ) * ((c₀ - a₀ - b₀ : ℤ) : ℝ) = ((nA * b₀ : ℤ) : ℝ) := by
        rw [← hk]; exact hcab_real
      exact_mod_cast h_real
    subst hN33
    have hNe' : a₀ + 2 * b₀ ≠ 33 := by simpa using hNe
    have hdvd33 : (a₀ + 2 * b₀) ∣ (33 : ℤ) := by simpa using hdvd_e
    have harea33 : b₀ * 33 = k ^ 2 * (a₀ + 2 * b₀) := by simpa using harea_int
    obtain ⟨h5, h3', h7, hk3⟩ := sporadic33 a₀ b₀ c₀ k ha0_pos hb0_pos hc0_pos hk_pos hc0_sq ha2b_ge3
      hdvd33 hNe' harea33
    have h5r : (a₀ : ℝ) = 5 := by exact_mod_cast h5
    have h3r : (b₀ : ℝ) = 3 := by exact_mod_cast h3'
    have h7r : (c₀ : ℝ) = 7 := by exact_mod_cast h7
    have hcb : c * b₀ = c₀ * b := by
      have : c = r * b := hcr
      rw [this]
      have h := hrnd
      push_cast [b₀, c₀] at h ⊢
      linear_combination b * h
    refine ⟨?_, ?_, ?_⟩
    · rw [ha_eq, h5r, h3r]; ring
    · rw [h3r, h7r] at hcb; linarith
    · rw [hk]; exact_mod_cast hk3

-- Local c²=a²+ab+b² proof (twoPiThree_c_sq in ThmIso is private)
private lemma twoPiThree_c_sq' {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha', -, hb', hγ, hc'⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha', hb', hc', hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith

-- Main theorem (the `IsoH9b` leaf is replaced by the sporadic data at `N = 33`)
set_option maxHeartbeats 800000 in
theorem iso33_key (D : CongruentDissection 33) (α a b c : ℝ) (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) (hisoTP : IsoTP D α) :
    ∃ (α' a' b' c' μ : ℝ), D.model.TwoPiThreeData α' a' b' c' ∧ D.target.BaseAlphaData α' a' b' c' μ ∧
      a' * 3 = 5 * b' ∧ c' * 3 = 7 * b' ∧ μ = 3 := by
  obtain ⟨_, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : c ^ 2 = a ^ 2 + a * b + b ^ 2 := twoPiThree_c_sq' hm
  obtain ⟨hiso_α, hiso_β⟩ := Row9.iso_closed_forms a b c hc2
  obtain ⟨hcamb_pos, hcbma_pos, Mα, Mβ, hMα_raw, hMβ_raw, hpMα, -, -⟩ :=
    Paper.cor_int_at D hα hm 0
  rw [fAlphaAt_zero] at hMα_raw; rw [fBetaAt_zero] at hMβ_raw
  -- Flux equations from lemmaCF sign cases
  have hA_eq : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fAlpha α hα).weight = μ*(a+2*b-2*c) →
      (Mα : ℝ) = (μ/b)*(c-a-b) := fun μ _ sgn => by
    rw [hMα_raw, sgn]; field_simp [hcamb_pos.ne', hb.ne']; nlinarith [hiso_α]
  have hA_neg : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fAlpha α hα).weight = -(μ*(a+2*b-2*c)) →
      ((-Mα : ℤ) : ℝ) = (μ/b)*(c-a-b) := fun μ _ sgn => by
    push_cast
    have hgoal : -(Mα : ℝ) = μ*(a+2*b-2*c) / (c+a-b) := by rw [hMα_raw, sgn]; ring
    rw [hgoal]; field_simp [hcamb_pos.ne', hb.ne']; nlinarith [hiso_α]
  have hB_eq : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fBeta α hα).weight = μ*(a+2*b+2*c) →
      (Mβ : ℝ) = (μ/b)*(c+a+b) := fun μ _ sgn => by
    rw [hMβ_raw, sgn]; field_simp [hcbma_pos.ne', hb.ne']; nlinarith [hiso_β]
  have hB_neg : ∀ μ : ℝ, 0 < μ →
      D.target.flux (fBeta α hα).weight = -(μ*(a+2*b+2*c)) →
      ((-Mβ : ℤ) : ℝ) = (μ/b)*(c+a+b) := fun μ _ sgn => by
    push_cast
    have hgoal : -(Mβ : ℝ) = μ*(a+2*b+2*c) / (c+b-a) := by rw [hMβ_raw, sgn]; ring
    rw [hgoal]; field_simp [hcbma_pos.ne', hb.ne']; nlinarith [hiso_β]
  rcases hisoTP with htgt | htgt
  -- Branch 1
  · obtain ⟨μ, hμ, hbase⟩ := base_alpha_of_isoTP D hm htgt
    have harea := Erdos634.Draft.ThmIso.base_alpha_area_identity D hm hbase ha hb hμ
    obtain hcf_α | hcf_α := Row9.lemmaCF_alpha D.target hα hbase <;>
    obtain hcf_β | hcf_β := Row9.lemmaCF_beta D.target hα hbase
    · exact ⟨_, _, _, _, μ, hm, hbase, thmIso_arith_bridge_b 33 rfl a b c μ ha hb hc hμ hc2 harea Mα Mβ
        (hA_eq μ hμ hcf_α) (hB_eq μ hμ hcf_β) hpMα⟩
    · exact ⟨_, _, _, _, μ, hm, hbase, thmIso_arith_bridge_b 33 rfl a b c μ ha hb hc hμ hc2 harea Mα (-Mβ)
        (hA_eq μ hμ hcf_α) (hB_neg μ hμ hcf_β) hpMα⟩
    · exact ⟨_, _, _, _, μ, hm, hbase, thmIso_arith_bridge_b 33 rfl a b c μ ha hb hc hμ hc2 harea (-Mα) Mβ
        (hA_neg μ hμ hcf_α) (hB_eq μ hμ hcf_β) (two_dvd_neg_sub hpMα)⟩
    · exact ⟨_, _, _, _, μ, hm, hbase, thmIso_arith_bridge_b 33 rfl a b c μ ha hb hc hμ hc2 harea (-Mα) (-Mβ)
        (hA_neg μ hμ hcf_α) (hB_neg μ hμ hcf_β) (two_dvd_neg_sub hpMα)⟩
  -- Branch 2
  · have hm' := twoPiThreeData_swap hm
    have hα' := irrPi_beta hα
    have htgt' : TgtAngles D (Real.pi/3-α) (Real.pi/3-α)
        ((Real.pi/3-α) + 3*(Real.pi/3-(Real.pi/3-α))) := by convert htgt using 2; ring
    obtain ⟨μ, hμ, hbase⟩ := base_alpha_of_isoTP D hm' htgt'
    have hc2' : c ^ 2 = b ^ 2 + b * a + a ^ 2 := by linarith [hc2, mul_comm a b]
    have harea := Erdos634.Draft.ThmIso.base_alpha_area_identity D hm' hbase hb ha hμ
    obtain ⟨hiso_α', hiso_β'⟩ := Row9.iso_closed_forms b a c hc2'
    obtain ⟨hcamb_pos', hcbma_pos', Mα', Mβ', hMα_raw', hMβ_raw', hpMα', -, -⟩ :=
      Paper.cor_int_at D hα' hm' 0
    rw [fAlphaAt_zero] at hMα_raw'; rw [fBetaAt_zero] at hMβ_raw'
    have hA_eq' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fAlpha (Real.pi/3-α) hα').weight = μ*(b+2*a-2*c) →
        (Mα' : ℝ) = (μ/a)*(c-b-a) := fun μ _ sgn => by
      rw [hMα_raw', sgn]; field_simp [hcamb_pos'.ne', ha.ne']; nlinarith [hiso_α']
    have hA_neg' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fAlpha (Real.pi/3-α) hα').weight = -(μ*(b+2*a-2*c)) →
        ((-Mα' : ℤ) : ℝ) = (μ/a)*(c-b-a) := fun μ _ sgn => by
      push_cast
      have hgoal : -(Mα' : ℝ) = μ*(b+2*a-2*c) / (c+b-a) := by rw [hMα_raw', sgn]; ring
      rw [hgoal]; field_simp [hcamb_pos'.ne', ha.ne']; nlinarith [hiso_α']
    have hB_eq' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fBeta (Real.pi/3-α) hα').weight = μ*(b+2*a+2*c) →
        (Mβ' : ℝ) = (μ/a)*(c+b+a) := fun μ _ sgn => by
      rw [hMβ_raw', sgn]; field_simp [hcbma_pos'.ne', ha.ne']; nlinarith [hiso_β']
    have hB_neg' : ∀ μ : ℝ, 0 < μ →
        D.target.flux (fBeta (Real.pi/3-α) hα').weight = -(μ*(b+2*a+2*c)) →
        ((-Mβ' : ℤ) : ℝ) = (μ/a)*(c+b+a) := fun μ _ sgn => by
      push_cast
      have hgoal : -(Mβ' : ℝ) = μ*(b+2*a+2*c) / (c+a-b) := by rw [hMβ_raw', sgn]; ring
      rw [hgoal]; field_simp [hcbma_pos'.ne', ha.ne']; nlinarith [hiso_β']
    obtain hcf_α | hcf_α := Row9.lemmaCF_alpha D.target hα' hbase <;>
    obtain hcf_β | hcf_β := Row9.lemmaCF_beta D.target hα' hbase
    · exact ⟨_, _, _, _, μ, hm', hbase, thmIso_arith_bridge_b 33 rfl b a c μ hb ha hc hμ hc2' harea Mα' Mβ'
        (hA_eq' μ hμ hcf_α) (hB_eq' μ hμ hcf_β) hpMα'⟩
    · exact ⟨_, _, _, _, μ, hm', hbase, thmIso_arith_bridge_b 33 rfl b a c μ hb ha hc hμ hc2' harea Mα' (-Mβ')
        (hA_eq' μ hμ hcf_α) (hB_neg' μ hμ hcf_β) hpMα'⟩
    · exact ⟨_, _, _, _, μ, hm', hbase, thmIso_arith_bridge_b 33 rfl b a c μ hb ha hc hμ hc2' harea (-Mα') Mβ'
        (hA_neg' μ hμ hcf_α) (hB_eq' μ hμ hcf_β) (two_dvd_neg_sub hpMα')⟩
    · exact ⟨_, _, _, _, μ, hm', hbase, thmIso_arith_bridge_b 33 rfl b a c μ hb ha hc hμ hc2' harea (-Mα') (-Mβ')
        (hA_neg' μ hμ hcf_α) (hB_neg' μ hμ hcf_β) (two_dvd_neg_sub hpMα')⟩


theorem finish33 (D : CongruentDissection 33) {α a b c μ : ℝ} (hm : D.model.TwoPiThreeData α a b c)
    (hbase : D.target.BaseAlphaData α a b c μ) (h1 : a * 3 = 5 * b) (h2 : c * 3 = 7 * b) (h3 : μ = 3) :
    ∃ D' : CongruentDissection 33,
      (∃ σ : Equiv.Perm (Fin 3), D'.target.oppLen (σ 0) = 21 ∧ D'.target.oppLen (σ 1) = 21 ∧
        D'.target.oppLen (σ 2) = 33) ∧
      ∃ τ : Equiv.Perm (Fin 3), D'.model.oppLen (τ 0) = 5 ∧ D'.model.oppLen (τ 1) = 3 ∧
        D'.model.oppLen (τ 2) = 7 := by
  obtain ⟨_, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  obtain ⟨-, σ, -, s0, -, s1, -, s2⟩ := hbase
  have hr : (3 / b : ℝ) ≠ 0 := by positivity
  have habs : |(3 / b : ℝ)| = 3 / b := abs_of_pos (by positivity)
  refine ⟨Erdos634.Realizable.scaleDissection 0 (3 / b) hr D, ⟨σ, ?_, ?_, ?_⟩, ?_⟩
  · rw [Erdos634.Geometry.SIX.tgt_oppLen_scale, habs, s0, h3]; field_simp; linarith
  · rw [Erdos634.Geometry.SIX.tgt_oppLen_scale, habs, s1, h3]; field_simp; linarith
  · rw [Erdos634.Geometry.SIX.tgt_oppLen_scale, habs, s2, h3]; field_simp; linarith
  · obtain ⟨τ, -, o0, -, o1, -, o2⟩ := hm
    refine ⟨τ, ?_, ?_, ?_⟩
    · rw [Erdos634.Geometry.SIX.mod_oppLen_scale, habs, o0]; field_simp; linarith
    · rw [Erdos634.Geometry.SIX.mod_oppLen_scale, habs, o1]; field_simp
    · rw [Erdos634.Geometry.SIX.mod_oppLen_scale, habs, o2]; field_simp; linarith

/-- **The geometric instance at N = 33**: rescaled, model sides `(5,3,7)`, target sides `(21,21,33)`. -/
theorem iso33_scaled (D : CongruentDissection 33) (α a b c : ℝ) (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) (hisoTP : IsoTP D α) :
    ∃ D' : CongruentDissection 33,
      (∃ σ : Equiv.Perm (Fin 3), D'.target.oppLen (σ 0) = 21 ∧ D'.target.oppLen (σ 1) = 21 ∧
        D'.target.oppLen (σ 2) = 33) ∧
      ∃ τ : Equiv.Perm (Fin 3), D'.model.oppLen (τ 0) = 5 ∧ D'.model.oppLen (τ 1) = 3 ∧
        D'.model.oppLen (τ 2) = 7 := by
  obtain ⟨α', a', b', c', μ, hm', hbase, h1, h2, h3⟩ := iso33_key D α a b c hα hm hisoTP
  exact finish33 D hm' hbase h1 h2 h3

end Erdos634.Draft.SIXIso33

#print axioms Erdos634.Draft.SIXIso33.iso33_scaled
