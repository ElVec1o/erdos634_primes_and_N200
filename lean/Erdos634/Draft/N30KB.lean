/-
N30K-B: soundness of the constant-`fac` checker `GA2RK.tgtOkF` / `chkTileF` (copy of GA2RB.tgtOk_sound with 15 replaced by a parameter `fac`).
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2RK

namespace Erdos634.N30K

open Erdos634.GA2R

section real

variable (n : ℕ) (sl sh : ℕ → ℕ)

set_option maxHeartbeats 1600000 in
/-- **Theorem K (soundness of `tgtOk`).** -/
theorem tgtOkF_sound (fac : ℕ) (htab : Tab n sl sh) {t1 t2 t3 A B C : ℕ} (h1 : t1 ≤ n) (h2 : t2 ≤ n) (h3 : t3 ≤ n)
    (hA : A ≤ n) (hB : B ≤ n) (hC : C ≤ n) (hok : tgtOkF fac sl sh t1 t2 t3 A B C = true)
    (m1 m2 m3 : ℕ)
    (hid : ((m1 : ℝ) * Real.sin (t1 * Real.pi / n) + m2 * Real.sin (t2 * Real.pi / n) +
        m3 * Real.sin (t3 * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
      = (fac : ℝ) * Real.sin (A * Real.pi / n) * Real.sin (t1 * Real.pi / n) * Real.sin (t2 * Real.pi / n) *
        Real.sin (t3 * Real.pi / n)) : False := by
  unfold tgtOkF at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hDL, p1⟩, p2⟩, p3⟩, q3⟩, hqh⟩, hql⟩, hns⟩ := hok
  set NH := fac * sh A * sh t1 * sh t2 * sh t3 with hNH
  set DL := sl B * sl C with hDLd
  set NL := fac * sl A * sl t1 * sl t2 * sl t3 with hNL
  set DH := sh B * sh C with hDH
  set qh := isqrt (NH / DL) + 1 with hqhd
  set ql := isqrt (NL / DH) with hqld
  -- real quantities
  set sA := 2 ^ 32 * Real.sin (A * Real.pi / n) with hsA
  set sB := 2 ^ 32 * Real.sin (B * Real.pi / n) with hsB
  set sC := 2 ^ 32 * Real.sin (C * Real.pi / n) with hsC
  set s1 := 2 ^ 32 * Real.sin (t1 * Real.pi / n) with hs1
  set s2 := 2 ^ 32 * Real.sin (t2 * Real.pi / n) with hs2
  set s3 := 2 ^ 32 * Real.sin (t3 * Real.pi / n) with hs3
  obtain ⟨lA, uA⟩ := htab A hA
  obtain ⟨lB, uB⟩ := htab B hB
  obtain ⟨lC, uC⟩ := htab C hC
  obtain ⟨l1, u1⟩ := htab t1 h1
  obtain ⟨l2, u2⟩ := htab t2 h2
  obtain ⟨l3, u3⟩ := htab t3 h3
  change (sl A : ℝ) ≤ sA at lA
  change sA ≤ (sh A : ℝ) at uA
  change (sl B : ℝ) ≤ sB at lB
  change sB ≤ (sh B : ℝ) at uB
  change (sl C : ℝ) ≤ sC at lC
  change sC ≤ (sh C : ℝ) at uC
  change (sl t1 : ℝ) ≤ s1 at l1
  change s1 ≤ (sh t1 : ℝ) at u1
  change (sl t2 : ℝ) ≤ s2 at l2
  change s2 ≤ (sh t2 : ℝ) at u2
  change (sl t3 : ℝ) ≤ s3 at l3
  change s3 ≤ (sh t3 : ℝ) at u3
  have z : ∀ k : ℕ, (0 : ℝ) ≤ k := fun k => Nat.cast_nonneg k
  -- scaled identity
  set Y : ℝ := m1 * s1 + m2 * s2 + m3 * s3 with hY
  have hscaled : Y ^ 2 * sB * sC = (fac : ℝ) * sA * s1 * s2 * s3 := by
    have e := congrArg (fun r => (2 : ℝ) ^ 128 * r) hid
    simp only [hY, hsA, hsB, hsC, hs1, hs2, hs3] at e ⊢
    linear_combination e
  have hY0 : 0 ≤ Y := by
    have a1 : (0 : ℝ) ≤ s1 := le_trans (z _) l1
    have a2 : (0 : ℝ) ≤ s2 := le_trans (z _) l2
    have a3 : (0 : ℝ) ≤ s3 := le_trans (z _) l3
    rw [hY]; positivity
  have a1 : (0 : ℝ) ≤ sA := le_trans (z _) lA
  have b1 : (0 : ℝ) ≤ sB := le_trans (z _) lB
  have c1 : (0 : ℝ) ≤ sC := le_trans (z _) lC
  have d1 : (0 : ℝ) ≤ s1 := le_trans (z _) l1
  have d2 : (0 : ℝ) ≤ s2 := le_trans (z _) l2
  have d3 : (0 : ℝ) ≤ s3 := le_trans (z _) l3
  -- upper bound  Y <= qh
  have hup : Y ≤ qh := by
    have hDLr : (0 : ℝ) < (DL : ℝ) := by exact_mod_cast hDL
    have step1 : (DL : ℝ) ≤ sB * sC := by
      rw [hDLd]; push_cast; exact mul_le_mul lB lC (z _) b1
    have step2 : (fac : ℝ) * sA * s1 * s2 * s3 ≤ (NH : ℝ) := by
      rw [hNH]; push_cast
      have t1' := mul_le_mul uA u1 d1 (z _)
      have t2' := mul_le_mul t1' u2 d2 (mul_nonneg (z _) (z _))
      have t3' := mul_le_mul t2' u3 d3 (mul_nonneg (mul_nonneg (z _) (z _)) (z _))
      have t4' := mul_le_mul_of_nonneg_left t3' (z fac)
      linarith [t4']
    have step3 : (NH : ℝ) ≤ (qh : ℝ) ^ 2 * DL := by
      have : NH ≤ qh * qh * DL := hqh
      have : (NH : ℝ) ≤ (qh : ℝ) * qh * DL := by exact_mod_cast this
      linarith [this, show (qh : ℝ) ^ 2 = qh * qh by ring]
    have : Y ^ 2 * DL ≤ (qh : ℝ) ^ 2 * DL := by
      calc Y ^ 2 * DL ≤ Y ^ 2 * (sB * sC) := mul_le_mul_of_nonneg_left step1 (sq_nonneg _)
        _ = Y ^ 2 * sB * sC := by ring
        _ = (fac : ℝ) * sA * s1 * s2 * s3 := hscaled
        _ ≤ NH := step2
        _ ≤ _ := step3
    have h2 : Y ^ 2 ≤ (qh : ℝ) ^ 2 := le_of_mul_le_mul_right this hDLr
    exact le_of_sq_le_sq h2 (z _)
  -- lower bound  ql <= Y
  have hlow : (ql : ℝ) ≤ Y := by
    have hDHr : (0 : ℝ) < (DH : ℝ) := by
      have hDLr : (0 : ℝ) < (DL : ℝ) := by exact_mod_cast hDL
      have s1' : (DL : ℝ) ≤ sB * sC := by
        rw [hDLd]; push_cast; exact mul_le_mul lB lC (z _) b1
      have s2' : sB * sC ≤ (DH : ℝ) := by
        rw [hDH]; push_cast; exact mul_le_mul uB uC c1 (z _)
      linarith
    have step1 : sB * sC ≤ (DH : ℝ) := by
      rw [hDH]; push_cast; exact mul_le_mul uB uC c1 (z _)
    have step2 : (NL : ℝ) ≤ (fac : ℝ) * sA * s1 * s2 * s3 := by
      rw [hNL]; push_cast
      have t1' := mul_le_mul lA l1 (z _) a1
      have t2' := mul_le_mul t1' l2 (z _) (mul_nonneg a1 d1)
      have t3' := mul_le_mul t2' l3 (z _) (mul_nonneg (mul_nonneg a1 d1) d2)
      have t4' := mul_le_mul_of_nonneg_left t3' (z fac)
      linarith [t4']
    have step3 : (ql : ℝ) ^ 2 * DH ≤ NL := by
      have : ql * ql * DH ≤ NL := hql
      have : (ql : ℝ) * ql * DH ≤ NL := by exact_mod_cast this
      linarith [this, show (ql : ℝ) ^ 2 = ql * ql by ring]
    have : (ql : ℝ) ^ 2 * DH ≤ Y ^ 2 * DH := by
      calc (ql : ℝ) ^ 2 * DH ≤ NL := step3
        _ ≤ (fac : ℝ) * sA * s1 * s2 * s3 := step2
        _ = Y ^ 2 * sB * sC := hscaled.symm
        _ = Y ^ 2 * (sB * sC) := by ring
        _ ≤ Y ^ 2 * DH := mul_le_mul_of_nonneg_left step1 (sq_nonneg _)
    have h2 : (ql : ℝ) ^ 2 ≤ Y ^ 2 := le_of_mul_le_mul_right this hDHr
    exact le_of_sq_le_sq h2 hY0
  -- sums
  have hsumL : (m1 : ℝ) * sl t1 + m2 * sl t2 + m3 * sl t3 ≤ Y := by
    rw [hY]
    have := mul_le_mul_of_nonneg_left l1 (z m1)
    have := mul_le_mul_of_nonneg_left l2 (z m2)
    have := mul_le_mul_of_nonneg_left l3 (z m3)
    linarith
  have hsumH : Y ≤ (m1 : ℝ) * sh t1 + m2 * sh t2 + m3 * sh t3 := by
    rw [hY]
    have := mul_le_mul_of_nonneg_left u1 (z m1)
    have := mul_le_mul_of_nonneg_left u2 (z m2)
    have := mul_le_mul_of_nonneg_left u3 (z m3)
    linarith
  have hN1 : m1 * sl t1 + m2 * sl t2 + m3 * sl t3 ≤ qh := by
    have : ((m1 * sl t1 + m2 * sl t2 + m3 * sl t3 : ℕ) : ℝ) ≤ (qh : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  have hN2 : ql ≤ m1 * sh t1 + m2 * sh t2 + m3 * sh t3 := by
    have : (ql : ℝ) ≤ ((m1 * sh t1 + m2 * sh t2 + m3 * sh t3 : ℕ) : ℝ) := by
      push_cast; linarith
    exact_mod_cast this
  exact noSol_sound p1 p2 p3 q3 hns m1 m2 m3 hN1 hN2

end real

#print axioms tgtOkF_sound

end Erdos634.N30K
