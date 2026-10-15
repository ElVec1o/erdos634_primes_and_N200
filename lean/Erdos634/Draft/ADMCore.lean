-- Tiling-level admissibility theorem: from a `CongruentDissection` of the
-- base-alpha (resp. base-beta) isosceles target by the tile `s*(a,b,c)` (primitive 120-degree triple, `s>0` a
-- real similarity scale; the paper has `s = 1`), derive `k = d e w`, `N = d w^2 (a+2b)`, `e | w(c-a-b)`,
-- `w(c-a-b)/e = N (mod 2)`.  Combines: area identity (`ThmIso.base_alpha_area_identity`), `cor:int`
-- (`Paper.cor_int_at`), flux closed forms (`Row9.lemmaCF_*`), and `FDDSpectrum.admissible_arith`.
import Erdos634.Draft.ThmIso
import Erdos634.Draft.ThmIsoShBridge
import Erdos634.Draft.FluxPaperCorIntAnchored
import Erdos634.Draft.FluxE2Pi3Row9
import Erdos634.Draft.FluxERow9Arith
import Erdos634.Draft.FDDSpectrumArith
import Erdos634.Draft.G3CAng

open scoped Classical

namespace Erdos634.Draft.ADMCore

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

/-! ## Pure arithmetic: integrality of the scale from the two flux invariants -/

theorem scale_int (N a b c : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (μ : ℝ) (hμ : 0 < μ)
    (harea : (N : ℝ) * b = μ ^ 2 * (a + 2 * b)) (nA nB : ℤ)
    (hA : (nA : ℝ) = (μ / b) * ((c : ℝ) - a - b))
    (hB : (nB : ℝ) = (μ / b) * ((c : ℝ) + a + b)) :
    ∃ k : ℕ, 0 < k ∧ μ = k ∧ N * b = k ^ 2 * (a + 2 * b) ∧
      (nA : ℤ) * b = k * ((c : ℤ) - a - b) := by
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hcR : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2 := by exact_mod_cast hc
  have hA' : (nA : ℝ) * b = μ * ((c : ℝ) - a - b) := by rw [hA]; field_simp
  have hB' : (nB : ℝ) * b = μ * ((c : ℝ) + a + b) := by rw [hB]; field_simp
  have hr_ne : ((c : ℤ) - a - b) ≠ 0 := by
    intro h0
    have hcab : (c : ℤ) = a + b := by linarith
    have hcZ : (c : ℤ) ^ 2 = (a : ℤ) ^ 2 + a * b + (b : ℤ) ^ 2 := by exact_mod_cast hc
    rw [hcab] at hcZ
    have : (a : ℤ) * b = 0 := by nlinarith
    have hpos : (0 : ℤ) < (a : ℤ) * b := by positivity
    omega
  have hr_R : (((c : ℤ) - a - b : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hr_ne
  have hp : ((nA : ℝ) * b) * ((nB : ℝ) * b) =
      (μ * ((c : ℝ) - a - b)) * (μ * ((c : ℝ) + a + b)) := by rw [hA', hB']
  have h2mu2 : 2 * μ ^ 2 = (N : ℝ) + nA * nB := by
    have h0 : (b : ℝ) ^ 2 * (2 * μ ^ 2 - N - nA * nB) = 0 := by
      linear_combination (-(b : ℝ)) * harea + (-1) * hp + (-μ ^ 2) * hcR
    have := (mul_eq_zero.mp h0).resolve_left (pow_ne_zero 2 hbR)
    linarith
  let qμ : ℚ := ((nA * b : ℤ) : ℚ) / (((c : ℤ) - a - b : ℤ) : ℚ)
  have hqmu_eq : μ = qμ := by
    rw [show (qμ : ℝ) = ((nA * b : ℤ) : ℝ) / (((c : ℤ) - a - b : ℤ) : ℝ) by simp [qμ]]
    rw [eq_comm, div_eq_iff hr_R]
    push_cast
    linarith [hA']
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
  lift k to ℕ using hk_pos.le
  have hk' : μ = (k : ℝ) := by rw [hk]; norm_cast
  refine ⟨k, by exact_mod_cast hk_pos, hk', ?_, ?_⟩
  · have h1 : (N : ℝ) * b = (k : ℝ) ^ 2 * (a + 2 * b) := by rw [← hk']; exact harea
    exact_mod_cast h1
  · have h1 : (nA : ℝ) * b = (k : ℝ) * ((c : ℝ) - a - b) := by rw [← hk']; exact hA'
    exact_mod_cast h1

/-! ## Geometry: the two integral invariants of the base-alpha target (via `cor:int`) -/

theorem twoPiThree_c_sq' {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
    c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨σ, -, ha', -, hb', hγ, hc'⟩ := h
  have hlc := T.lawCos_perm σ
  rw [ha', hb', hc', hγ, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 from by ring,
      Real.cos_pi_sub, Real.cos_pi_div_three] at hlc
  linarith

theorem flux_invariants {N : ℕ} (D : CongruentDissection N) {α A B C μ : ℝ}
    (hα : IrrPi α) (hm : D.model.TwoPiThreeData α A B C)
    (hbase : D.target.BaseAlphaData α A B C μ) :
    ∃ nA nB : ℤ, (nA : ℝ) = (μ / B) * (C - A - B) ∧ (nB : ℝ) = (μ / B) * (C + A + B) ∧
      (2 : ℤ) ∣ nA - N := by
  obtain ⟨-, hc, ha, hb⟩ := cos_alpha_of_TwoPiThree D.model hm
  have hc2 : C ^ 2 = A ^ 2 + A * B + B ^ 2 := twoPiThree_c_sq' hm
  obtain ⟨hiso_α, hiso_β⟩ := Row9.iso_closed_forms A B C hc2
  obtain ⟨hcamb_pos, hcbma_pos, Mα, Mβ, hMα_raw, hMβ_raw, hpα, -, -⟩ :=
    Paper.cor_int_at D hα hm 0
  rw [fAlphaAt_zero] at hMα_raw; rw [fBetaAt_zero] at hMβ_raw
  obtain ⟨nA, hnA, hpar⟩ : ∃ nA : ℤ, (nA : ℝ) = (μ / B) * (C - A - B) ∧ (2 : ℤ) ∣ nA - N := by
    rcases Row9.lemmaCF_alpha D.target hα hbase with sgn | sgn
    · refine ⟨Mα, ?_, hpα⟩
      rw [hMα_raw, sgn]; field_simp [hcamb_pos.ne', hb.ne']; first | linear_combination (-μ) * hiso_α | linear_combination μ * hiso_α
    · refine ⟨-Mα, ?_, ?_⟩
      · push_cast
        have hgoal : -(Mα : ℝ) = μ * (A + 2 * B - 2 * C) / (C + A - B) := by
          rw [hMα_raw, sgn]; ring
        rw [hgoal]; field_simp [hcamb_pos.ne', hb.ne']; first | linear_combination (-μ) * hiso_α | linear_combination μ * hiso_α
      · rw [show -Mα - (N : ℤ) = -(Mα - N) - 2 * N by ring]
        exact dvd_sub (dvd_neg.mpr hpα) (dvd_mul_right 2 _)
  obtain ⟨nB, hnB⟩ : ∃ nB : ℤ, (nB : ℝ) = (μ / B) * (C + A + B) := by
    rcases Row9.lemmaCF_beta D.target hα hbase with sgn | sgn
    · refine ⟨Mβ, ?_⟩
      rw [hMβ_raw, sgn]; field_simp [hcbma_pos.ne', hb.ne']; first | linear_combination (-μ) * hiso_β | linear_combination μ * hiso_β
    · refine ⟨-Mβ, ?_⟩
      push_cast
      have hgoal : -(Mβ : ℝ) = μ * (A + 2 * B + 2 * C) / (C + B - A) := by
        rw [hMβ_raw, sgn]; ring
      rw [hgoal]; field_simp [hcbma_pos.ne', hb.ne']; first | linear_combination (-μ) * hiso_β | linear_combination μ * hiso_β
  exact ⟨nA, nB, hnA, hnB, hpar⟩

/-! ## `alpha` irrational is automatic for an integer 120-degree triple -/

theorem irrPi_of_triple (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc0 : 0 < c)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2) (α : ℝ)
    (hcos : Real.cos α = ((a : ℝ) + 2 * b) / (2 * c)) : IrrPi α := by
  have hcR : (c : ℝ) ^ 2 = (a : ℝ) ^ 2 + a * b + (b : ℝ) ^ 2 := by exact_mod_cast hc
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hcR0 : (0 : ℝ) < c := by exact_mod_cast hc0
  refine Erdos634.Draft.G3CAng.irrPi_of_cos α (((a : ℚ) + 2 * b) / (2 * c)) (by rw [hcos]; push_cast; rfl)
    ?_ ?_ ?_ ?_ ?_
  · have : (0 : ℚ) < ((a : ℚ) + 2 * b) / (2 * c) := by positivity
    exact this.ne'
  · intro h
    have h' : ((a : ℚ) + 2 * b) = 2 * c := by
      field_simp at h; linarith
    have h'' : ((a : ℝ) + 2 * b) = 2 * c := by exact_mod_cast h'
    nlinarith
  · intro h
    have : (0 : ℚ) < ((a : ℚ) + 2 * b) / (2 * c) := by positivity
    linarith
  · intro h
    have h' : 2 * ((a : ℚ) + 2 * b) = 2 * c := by
      field_simp at h; linarith
    have h'' : ((a : ℝ) + 2 * b) = c := by
      have : 2 * ((a : ℝ) + 2 * b) = 2 * c := by exact_mod_cast h'
      linarith
    nlinarith
  · intro h
    have : (0 : ℚ) < ((a : ℚ) + 2 * b) / (2 * c) := by positivity
    linarith

/-! ## The tiling-level theorem, base-alpha -/

theorem admissible_alpha {N : ℕ} (D : CongruentDissection N) (a b c d e : ℕ) (s α μ : ℝ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hbde : b = d * e ^ 2) (hd : Squarefree d)
    (hm : D.model.TwoPiThreeData α (s * a) (s * b) (s * c))
    (hbase : D.target.BaseAlphaData α (s * a) (s * b) (s * c) μ) :
    ∃ k w : ℕ, μ = k ∧ 0 < w ∧ N * b = k ^ 2 * (a + 2 * b) ∧ k = d * e * w ∧
      N = d * w ^ 2 * (a + 2 * b) ∧ (e : ℤ) ∣ w * ((c : ℤ) - a - b) ∧
      (2 : ℤ) ∣ (w * ((c : ℤ) - a - b)) / (e : ℤ) - N := by
  obtain ⟨hcos, hc0, ha0, hb0⟩ := cos_alpha_of_TwoPiThree D.model hm
  have ha : 0 < a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · subst h; simp at ha0
    · exact h
  have hb : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · subst h; simp at hb0
    · exact h
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hs : 0 < s := (pos_iff_pos_of_mul_pos ha0).mpr haR
  have hc00 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · subst h; simp at hc0
    · exact h
  have hα : IrrPi α := by
    refine irrPi_of_triple a b c ha hb hc00 hc α ?_
    rw [hcos]; field_simp
  have harea0 := Erdos634.Draft.ThmIso.base_alpha_area_identity D hm hbase ha0 hb0 hbase.1
  have hμ := hbase.1
  have harea : (N : ℝ) * b = μ ^ 2 * (a + 2 * b) := by
    have hsne : s ≠ 0 := hs.ne'
    have : s * ((N : ℝ) * b) = s * (μ ^ 2 * (a + 2 * b)) := by linear_combination harea0
    exact mul_left_cancel₀ hsne this
  obtain ⟨nA, nB, hA0, hB0, hpar0⟩ := flux_invariants D hα hm hbase
  have hsne : s ≠ 0 := hs.ne'
  have hbR : (b : ℝ) ≠ 0 := by positivity
  have hA : (nA : ℝ) = (μ / b) * ((c : ℝ) - a - b) := by
    rw [hA0]; field_simp
  have hB : (nB : ℝ) = (μ / b) * ((c : ℝ) + a + b) := by
    rw [hB0]; field_simp
  obtain ⟨k, hk, hμk, harea', hM⟩ := scale_int N a b c ha hb hc μ hμ harea nA nB hA hB
  obtain ⟨w, hw, hkw, hN, hdv, -, hpar⟩ :=
    Erdos634.Draft.FDDSpectrum.admissible_arith a b c d e N k hb hcop hbde hd hk harea' nA hM hpar0
  exact ⟨k, w, hμk, hw, harea', hkw, hN, hdv, by
    have hq : (w * ((c : ℤ) - a - b)) / (e : ℤ) = nA := by
      have he0 : e ≠ 0 := by rintro rfl; simp at hbde; omega
      have hdz : (d : ℤ) * e ≠ 0 := by
        have : d ≠ 0 := hd.ne_zero
        positivity
      have hkZ : (k : ℤ) = d * e * w := by exact_mod_cast hkw
      have hbZ : (b : ℤ) = d * e ^ 2 := by exact_mod_cast hbde
      have hMe : nA * e = w * ((c : ℤ) - a - b) := by
        have h1 : (d : ℤ) * e * (nA * e) = (d : ℤ) * e * (w * ((c : ℤ) - a - b)) := by
          linear_combination hM - nA * hbZ + ((c : ℤ) - a - b) * hkZ
        exact mul_left_cancel₀ hdz h1
      rw [← hMe]; exact Int.mul_ediv_cancel nA (by exact_mod_cast he0)
    rw [hq]; exact hpar0⟩

/-! ## Base-beta: the same theorem for the swapped tile -/

theorem twoPiThreeData_swap {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c) :
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

/-- **`thm:admissible`, base-beta clause.**  The base-beta target is the base-alpha target of the
swapped tile `(pi/3 - alpha; s b, s a, s c)`; `a = d' e'^2`. -/
theorem admissible_beta {N : ℕ} (D : CongruentDissection N) (a b c d' e' : ℕ) (s α μ : ℝ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hade : a = d' * e' ^ 2) (hd : Squarefree d')
    (hm : D.model.TwoPiThreeData α (s * a) (s * b) (s * c))
    (hbase : D.target.BaseAlphaData (Real.pi / 3 - α) (s * b) (s * a) (s * c) μ) :
    ∃ k w : ℕ, μ = k ∧ 0 < w ∧ N * a = k ^ 2 * (b + 2 * a) ∧ k = d' * e' * w ∧
      N = d' * w ^ 2 * (2 * a + b) ∧ (e' : ℤ) ∣ w * ((c : ℤ) - a - b) ∧
      (2 : ℤ) ∣ (w * ((c : ℤ) - a - b)) / (e' : ℤ) - N := by
  have hm' := twoPiThreeData_swap hm
  obtain ⟨k, w, h1, h2, h3, h4, h5, h6, h7⟩ :=
    admissible_alpha D b a c d' e' s (Real.pi / 3 - α) μ hcop.symm
      (by rw [hc]; ring) hade hd hm' hbase
  refine ⟨k, w, h1, h2, h3, h4, ?_, ?_, ?_⟩
  · rw [h5]; ring
  · have : ((c : ℤ) - b - a) = (c : ℤ) - a - b := by ring
    rw [this] at h6; exact h6
  · have : ((c : ℤ) - b - a) = (c : ℤ) - a - b := by ring
    rw [this] at h7; exact h7

/-! ## Angle-form wrappers: the target is "the base-alpha (resp. base-beta) isosceles triangle" -/

theorem admissible_alpha_tgt {N : ℕ} (D : CongruentDissection N) (a b c d e : ℕ) (s α : ℝ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hbde : b = d * e ^ 2) (hd : Squarefree d)
    (hm : D.model.TwoPiThreeData α (s * a) (s * b) (s * c))
    (ht : TgtAngles D α α (α + 3 * (Real.pi / 3 - α))) :
    ∃ k w : ℕ, D.target.BaseAlphaData α (s * a) (s * b) (s * c) (k : ℝ) ∧ 0 < w ∧
      k = d * e * w ∧ N = d * w ^ 2 * (a + 2 * b) ∧ (e : ℤ) ∣ w * ((c : ℤ) - a - b) ∧
      (2 : ℤ) ∣ (w * ((c : ℤ) - a - b)) / (e : ℤ) - N := by
  obtain ⟨μ, -, hbase⟩ := base_alpha_of_isoTP D hm ht
  obtain ⟨k, w, hμk, hw, -, hkw, hN, hdv, hpar⟩ := admissible_alpha D a b c d e s α μ hcop hc hbde hd hm hbase
  exact ⟨k, w, hμk ▸ hbase, hw, hkw, hN, hdv, hpar⟩

theorem admissible_beta_tgt {N : ℕ} (D : CongruentDissection N) (a b c d' e' : ℕ) (s α : ℝ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hade : a = d' * e' ^ 2) (hd : Squarefree d')
    (hm : D.model.TwoPiThreeData α (s * a) (s * b) (s * c))
    (ht : TgtAngles D (Real.pi / 3 - α) (Real.pi / 3 - α)
      ((Real.pi / 3 - α) + 3 * (Real.pi / 3 - (Real.pi / 3 - α)))) :
    ∃ k w : ℕ, D.target.BaseAlphaData (Real.pi / 3 - α) (s * b) (s * a) (s * c) (k : ℝ) ∧ 0 < w ∧
      k = d' * e' * w ∧ N = d' * w ^ 2 * (2 * a + b) ∧ (e' : ℤ) ∣ w * ((c : ℤ) - a - b) ∧
      (2 : ℤ) ∣ (w * ((c : ℤ) - a - b)) / (e' : ℤ) - N := by
  have hm' := twoPiThreeData_swap hm
  obtain ⟨μ, -, hbase⟩ := base_alpha_of_isoTP D hm' ht
  obtain ⟨k, w, hμk, hw, -, hkw, hN, hdv, hpar⟩ :=
    admissible_beta D a b c d' e' s α μ hcop hc hade hd hm hbase
  exact ⟨k, w, hμk ▸ hbase, hw, hkw, hN, hdv, hpar⟩

end Erdos634.Draft.ADMCore

#print axioms Erdos634.Draft.ADMCore.scale_int
#print axioms Erdos634.Draft.ADMCore.flux_invariants
#print axioms Erdos634.Draft.ADMCore.irrPi_of_triple
#print axioms Erdos634.Draft.ADMCore.admissible_alpha
#print axioms Erdos634.Draft.ADMCore.admissible_beta
#print axioms Erdos634.Draft.ADMCore.admissible_alpha_tgt
#print axioms Erdos634.Draft.ADMCore.admissible_beta_tgt
