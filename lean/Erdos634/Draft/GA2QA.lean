/-
Assembly: `GapA2Residual` and `gapA2_of_residual : GapA2Residual -> GapA2`.

The (i,j,k)-case split of GapA2 (N = 15, Case A): every n with all prime factors < 7 and 15 | n is n = 2^i 3^j 5^k with j, k >= 1.
Proved (existing theorems):
  15 !| n                                 : GA2OBase.fifteen_dvd  (so j, k >= 1)
  n = 15 (i,j,k) = (0,1,1)                : GA2OBase.gapA2_n15
  i >= 3 (any j, k >= 1)                  : GA2NSlice.gapA2_slice_i3
  i in {0,2}, k = 1, j >= 2               : GA2PH.gapA2_slice_i02   (Theorems B, C)
  n = 75 = (0,1,2), n = 90 = (1,2,1)      : GA2OFin2.gapA2_n75 / gapA2_n90 (single values)
Not covered (the residual hypothesis `ResidualIJK`):
  (R-30/60) j = k = 1, i in {1, 2}                         (n = 30, 60)
  (R-D)     i = 1, k = 1, j >= 2, (i,j,k) != (1,2,1)       (Prop D, and the case of an entry divisible by 3)
  (R-K)     k >= 2, i <= 2, j >= 1, (i,j,k) != (0,1,2)      (Props K-a (i=2), K-b (i=0), K-c (i=1))
No new mathematics; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2PH
import Erdos634.Draft.GA2OFin2
import Erdos634.Draft.GA2OBase

namespace Erdos634.GA2Q

open Erdos634.Geometry Erdos634.CaseA.R0c Erdos634.CaseA.R0c15

/-- 5-smooth numbers are 2^i 3^j 5^k. -/
theorem smooth_rep : ∀ n : ℕ, 0 < n → (∀ p : ℕ, p.Prime → p ∣ n → p < 7) →
    ∃ i j k : ℕ, n = 2 ^ i * 3 ^ j * 5 ^ k := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn h
    by_cases h1 : n = 1
    · exact ⟨0, 0, 0, by simp [h1]⟩
    · obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
      obtain ⟨m, rfl⟩ := hpn
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hlt : m < p * m := by
        have := hp.two_le
        nlinarith
      have hm' : ∀ q : ℕ, q.Prime → q ∣ m → q < 7 := fun q hq hqm => h q hq (Dvd.dvd.mul_left hqm p)
      obtain ⟨i, j, k, e⟩ := ih m hlt hm hm'
      have hp7 := h p hp (dvd_mul_right p m)
      have hp2 := hp.two_le
      interval_cases p
      · exact ⟨i + 1, j, k, by rw [e]; ring⟩
      · exact ⟨i, j + 1, k, by rw [e]; ring⟩
      · exfalso; revert hp; decide
      · exact ⟨i, j, k + 1, by rw [e]; ring⟩
      · exfalso; revert hp; decide

/-- The residual exponent triples: exactly the (i, j, k) not covered by the discharged pieces. -/
def ResidualIJK (i j k : ℕ) : Prop :=
  1 ≤ j ∧ 1 ≤ k ∧ i ≤ 2 ∧ (i, j, k) ≠ (0, 1, 2) ∧ (i, j, k) ≠ (1, 2, 1) ∧
    ((j = 1 ∧ k = 1 ∧ (i = 1 ∨ i = 2)) ∨ (i = 1 ∧ k = 1 ∧ 2 ≤ j) ∨ 2 ≤ k)

instance (i j k : ℕ) : Decidable (ResidualIJK i j k) := by unfold ResidualIJK; infer_instance

/-- **The residual hypothesis**: GapA2 restricted to the exponent triples that no discharged piece covers. -/
def GapA2Residual : Prop :=
  ∀ (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (i j k : ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ t, D.model.angleAt t = a t * Real.pi / n) →
    n = 2 ^ i * 3 ^ j * 5 ^ k → ResidualIJK i j k → False

theorem gapA2_of_residual (R : GapA2Residual) : Erdos634.CaseA.R0c15.GapA2 := by
  intro D n a hn hgcd ha hsm
  obtain ⟨i, j, k, e⟩ := smooth_rep n hn hsm
  have h15 := Erdos634.GA2OBase.fifteen_dvd D hn a ha
  have hj : 1 ≤ j := by
    by_contra hj0
    have hj0 : j = 0 := by omega
    have h3 : 3 ∣ n := Dvd.dvd.trans (by norm_num) h15
    have hc : Nat.Coprime 3 n := by
      rw [e, hj0]
      simp only [pow_zero, mul_one]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
        (Nat.Coprime.pow_right _ (by norm_num))
    have := Nat.Coprime.eq_one_of_dvd hc h3
    omega
  have hk : 1 ≤ k := by
    by_contra hk0
    have hk0 : k = 0 := by omega
    have h5 : 5 ∣ n := Dvd.dvd.trans (by norm_num) h15
    have hc : Nat.Coprime 5 n := by
      rw [e, hk0]
      simp only [pow_zero, mul_one]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
        (Nat.Coprime.pow_right _ (by norm_num))
    have := Nat.Coprime.eq_one_of_dvd hc h5
    omega
  by_cases hi3 : 3 ≤ i
  · exact Erdos634.GA2NSlice.gapA2_slice_i3 D n a hn hgcd ha
      ⟨k, i - 3, j, hk, hj, by rw [e]; rw [show i - 3 + 3 = i by omega]; ring⟩
  · by_cases hR : ResidualIJK i j k
    · exact R D n a i j k hn hgcd ha e hR
    · have hi : i ≤ 2 := by omega
      unfold ResidualIJK at hR
      have hne : ¬ ((i, j, k) ≠ (0, 1, 2) ∧ (i, j, k) ≠ (1, 2, 1) ∧
          ((j = 1 ∧ k = 1 ∧ (i = 1 ∨ i = 2)) ∨ (i = 1 ∧ k = 1 ∧ 2 ≤ j) ∨ 2 ≤ k)) := fun h => hR ⟨hj, hk, hi, h⟩
      by_cases hc1 : (i, j, k) = (0, 1, 2)
      · obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 := by simpa [Prod.ext_iff] using hc1
        exact Erdos634.GA2OFin2.gapA2_n75 D n a hn hgcd ha (by rw [e]; norm_num)
      by_cases hc2 : (i, j, k) = (1, 2, 1)
      · obtain ⟨rfl, rfl, rfl⟩ : i = 1 ∧ j = 2 ∧ k = 1 := by simpa [Prod.ext_iff] using hc2
        exact Erdos634.GA2OFin2.gapA2_n90 D n a hn hgcd ha (by rw [e]; norm_num)
      have hnr : ¬ ((j = 1 ∧ k = 1 ∧ (i = 1 ∨ i = 2)) ∨ (i = 1 ∧ k = 1 ∧ 2 ≤ j) ∨ 2 ≤ k) :=
        fun h => hne ⟨hc1, hc2, h⟩
      have hk1 : k = 1 := by omega
      subst hk1
      by_cases hj1 : j = 1
      · have hi0 : i = 0 := by omega
        subst hj1; subst hi0
        exact Erdos634.GA2OBase.gapA2_n15 D n a hn hgcd ha (by rw [e]; norm_num)
      · have hj2 : 2 ≤ j := by omega
        have hi02 : i = 0 ∨ i = 2 := by omega
        refine Erdos634.GA2PH.gapA2_slice_i02 D n a hn hgcd ha ?_
        rcases hi02 with rfl | rfl
        · exact Or.inl ⟨j, hj2, by rw [e]; ring⟩
        · exact Or.inr ⟨j, hj2, by rw [e]; ring⟩

/-! ### Witnesses and controls -/

/-- The residual is nonempty arithmetically: n = 30, 60 (j = k = 1), 90 j=3 (n = 270), 25*2 (K-c) ... -/
theorem residual_witnesses :
    ResidualIJK 1 1 1 ∧ ResidualIJK 2 1 1 ∧ ResidualIJK 1 3 1 ∧ ResidualIJK 0 1 3 ∧ ResidualIJK 0 2 2 ∧
    ResidualIJK 1 1 2 ∧ ResidualIJK 2 2 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold ResidualIJK <;> decide

/-- Negative controls: the discharged triples are NOT residual (so the case split is not vacuous the other way). -/
theorem discharged_not_residual :
    ¬ ResidualIJK 0 1 1 ∧ ¬ ResidualIJK 0 2 1 ∧ ¬ ResidualIJK 2 3 1 ∧ ¬ ResidualIJK 3 1 1 ∧
    ¬ ResidualIJK 5 2 4 ∧ ¬ ResidualIJK 0 1 2 ∧ ¬ ResidualIJK 1 2 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold ResidualIJK <;> decide

/-- Exhaustiveness check: for i, j, k <= 6 every triple with j, k >= 1 is residual or in a discharged row. -/
theorem partition_check : ∀ i ∈ Finset.range 7, ∀ j ∈ Finset.range 7, ∀ k ∈ Finset.range 7,
    1 ≤ j → 1 ≤ k →
    (3 ≤ i ∨ (i = 0 ∧ j = 1 ∧ k = 1) ∨ ((i = 0 ∨ i = 2) ∧ k = 1 ∧ 2 ≤ j) ∨ (i, j, k) = (0, 1, 2) ∨
      (i, j, k) = (1, 2, 1) ∨ ResidualIJK i j k) := by
  decide +kernel

end Erdos634.GA2Q

#print axioms Erdos634.GA2Q.smooth_rep
#print axioms Erdos634.GA2Q.gapA2_of_residual
#print axioms Erdos634.GA2Q.residual_witnesses
#print axioms Erdos634.GA2Q.discharged_not_residual
#print axioms Erdos634.GA2Q.partition_check
