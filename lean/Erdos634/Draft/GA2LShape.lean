/-
GA2L, atom P5: **shapes arithmetic** of GA2Y_NOTES Lemma A3 (last paragraph), general i = k+3 >= 3, j >= 0.

n = 2^(k+3) * (3^j * 5).  p, q distinct odd entries with a_p + a_q < n (the third entry is positive), and
the group-core output
    a_p = (-1)^s a_q (mod 5), (mod 3^j),   a_p = (-1)^s (1+2^(k+2))^e a_q (mod 2^(k+3)).
Then e = 1 and either s = 0 and |a_p - a_q| = n/2 (shape A) or s = 1 and a_p + a_q = n/2 (shape B).
Witnesses (n = 120, k = 0, j = 1): shape A (a_p, a_q) = (67, 7); shape B (53, 7); and the whole
statement was checked exhaustively in Python for k <= 2, j <= 3 (0 violations, 5460 solutions).
Formalization of paper-level mathematics; no sorry / native_decide.
-/
import Mathlib

namespace Erdos634.GA2LShape

theorem shape_e1 (T m D : ℤ) (hT : 0 < T) (hm : 0 < m) (hcop : IsCoprime m T) (h1 : m ∣ D)
    (h2 : 2 * T ∣ D - T) (hlt : |D| < 2 * T * m) : D = T * m ∨ D = -(T * m) := by
  obtain ⟨w, hw⟩ := h2
  have hD : D = T * (1 + 2 * w) := by linarith
  have hdv : m ∣ 1 + 2 * w := by
    have : m ∣ (1 + 2 * w) * T := by rw [mul_comm, ← hD]; exact h1
    exact hcop.dvd_of_dvd_mul_right this
  obtain ⟨v, hv⟩ := hdv
  have hD2 : D = T * m * v := by rw [hD, hv]; ring
  have hv0 : v ≠ 0 := by
    rintro rfl; omega
  have hTm : 0 < T * m := mul_pos hT hm
  have habs : |v| < 2 := by
    rw [hD2, abs_mul, abs_of_pos hTm] at hlt
    have : T * m * |v| < T * m * 2 := by nlinarith
    exact lt_of_mul_lt_mul_left this hTm.le
  have : v = 1 ∨ v = -1 := by
    rcases abs_lt.1 habs with ⟨a, b⟩
    omega
  rcases this with rfl | rfl
  · left; rw [hD2]; ring
  · right; rw [hD2]; ring

theorem shape_e0 (T m D : ℤ) (hT : 0 < T) (hm : 0 < m) (hcop : IsCoprime m (2 * T)) (h1 : m ∣ D)
    (h2 : 2 * T ∣ D) : 2 * T * m ∣ D := by
  have := hcop.symm.mul_dvd h2 h1
  exact this

theorem odd_cop (a : ℤ) (ha : Odd a) (k : ℕ) : IsCoprime a (2 ^ k) := by
  obtain ⟨b, hb⟩ := ha
  have h2 : IsCoprime a 2 := ⟨1, -b, by rw [hb]; ring⟩
  exact h2.pow_right

theorem shape_arith (k j : ℕ) (s e : ℕ) (hs : s < 2) (he : e < 2) (ap aq : ℤ)
    (hpo : Odd ap) (hqo : Odd aq) (hp : 0 < ap) (hq : 0 < aq)
    (hsum : ap + aq < 2 ^ (k + 3) * (3 ^ j * 5)) (hne : ap ≠ aq)
    (c5 : ap ≡ (-1) ^ s * aq [ZMOD 5]) (c3 : ap ≡ (-1) ^ s * aq [ZMOD 3 ^ j])
    (c2 : ap ≡ (-1) ^ s * aq * (1 + 2 ^ (k + 2)) ^ e [ZMOD 2 ^ (k + 3)]) :
    e = 1 ∧ ((s = 0 ∧ (ap = aq + 2 ^ (k + 2) * (3 ^ j * 5) ∨ aq = ap + 2 ^ (k + 2) * (3 ^ j * 5))) ∨
      (s = 1 ∧ ap + aq = 2 ^ (k + 2) * (3 ^ j * 5))) := by
  set T : ℤ := 2 ^ (k + 2) with hT
  set m : ℤ := 3 ^ j * 5 with hm
  have hTpos : 0 < T := by positivity
  have hmpos : 0 < m := by positivity
  have hn : (2 : ℤ) ^ (k + 3) = 2 * T := by rw [hT]; ring
  have hmo : Odd m := by
    have : Odd ((3 : ℤ) ^ j) := Odd.pow (by decide)
    exact this.mul (by decide)
  have hcopT : IsCoprime m T := odd_cop m hmo (k + 2)
  have hcop2T : IsCoprime m (2 * T) := by
    have : IsCoprime m 2 := by
      obtain ⟨b, hb⟩ := hmo
      exact ⟨1, -b, by rw [hb]; ring⟩
    exact this.mul_right hcopT
  rw [hn] at hsum c2
  -- m divides ap - (-1)^s aq
  have hm1 : m ∣ ap - (-1) ^ s * aq := by
    have d5 : (5 : ℤ) ∣ ap - (-1) ^ s * aq := (Int.modEq_iff_dvd.1 c5.symm)
    have d3 : (3 : ℤ) ^ j ∣ ap - (-1) ^ s * aq := (Int.modEq_iff_dvd.1 c3.symm)
    have hc : IsCoprime ((3 : ℤ) ^ j) 5 := by
      apply IsCoprime.pow_left
      exact ⟨2, -1, by norm_num⟩
    rw [hm, mul_comm]
    exact hc.symm.mul_dvd d5 d3
  have d2 : 2 * T ∣ ap - (-1) ^ s * aq * (1 + T) ^ e := by
    have := Int.modEq_iff_dvd.1 c2.symm
    exact this
  obtain ⟨b, hb⟩ := hqo
  obtain ⟨b', hb'⟩ := hpo
  have hsum' : ap + aq < 2 * T * m := by rw [hm]; nlinarith [hsum]
  have hN : 0 < 2 * T * m := by positivity
  have hq2 : 2 * T ∣ aq * T - T := ⟨b, by rw [hb]; ring⟩
  have hq3 : 2 * T ∣ aq * T + T := ⟨b + 1, by rw [hb]; ring⟩
  obtain rfl | rfl : s = 0 ∨ s = 1 := by omega
  · obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
    · exfalso
      norm_num at hm1 d2
      have h0 := shape_e0 T m (ap - aq) hTpos hmpos hcop2T hm1 d2
      have := Int.eq_zero_of_abs_lt_dvd h0 (by rw [abs_lt]; constructor <;> linarith)
      exact hne (by linarith)
    · norm_num at hm1 d2
      have h2 : 2 * T ∣ (ap - aq) - T := by
        have := dvd_add d2 hq2
        convert this using 1; ring
      have := shape_e1 T m (ap - aq) hTpos hmpos hcopT hm1 h2
        (by rw [abs_lt]; constructor <;> nlinarith)
      refine ⟨rfl, Or.inl ⟨rfl, ?_⟩⟩
      rcases this with h | h
      · left; linarith
      · right; linarith
  · obtain rfl | rfl : e = 0 ∨ e = 1 := by omega
    · exfalso
      norm_num at hm1 d2
      have hm1' : m ∣ ap + aq := by simpa using hm1
      have d2' : 2 * T ∣ ap + aq := by simpa using d2
      have h0 := shape_e0 T m (ap + aq) hTpos hmpos hcop2T hm1' d2'
      have := Int.eq_zero_of_abs_lt_dvd h0 (by rw [abs_lt]; constructor <;> linarith)
      linarith
    · norm_num at hm1 d2
      have hm1' : m ∣ ap + aq := by simpa using hm1
      have h2 : 2 * T ∣ (ap + aq) - T := by
        have := dvd_sub d2 hq3
        convert this using 1; ring
      have := shape_e1 T m (ap + aq) hTpos hmpos hcopT hm1' h2
        (by rw [abs_lt]; constructor <;> nlinarith)
      refine ⟨rfl, Or.inr ⟨rfl, ?_⟩⟩
      rcases this with h | h
      · linarith
      · exfalso; nlinarith

/-- Witnesses for the hypotheses (n = 120): shape A (67, 7) and shape B (53, 7). -/
example : (67 : ℤ) ≡ (-1) ^ 0 * 7 [ZMOD 5] ∧ (67 : ℤ) ≡ (-1) ^ 0 * 7 [ZMOD 3 ^ 1] ∧
    (67 : ℤ) ≡ (-1) ^ 0 * 7 * (1 + 2 ^ (0 + 2)) ^ 1 [ZMOD 2 ^ (0 + 3)] := by decide

example : (53 : ℤ) ≡ (-1) ^ 1 * 7 [ZMOD 5] ∧ (53 : ℤ) ≡ (-1) ^ 1 * 7 [ZMOD 3 ^ 1] ∧
    (53 : ℤ) ≡ (-1) ^ 1 * 7 * (1 + 2 ^ (0 + 2)) ^ 1 [ZMOD 2 ^ (0 + 3)] := by decide

end Erdos634.GA2LShape

#print axioms Erdos634.GA2LShape.shape_arith
