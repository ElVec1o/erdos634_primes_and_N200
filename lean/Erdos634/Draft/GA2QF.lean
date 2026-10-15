/-
Assembly: `GapA2Residual2` and `gapA2_of_residual2 : GapA2Residual2 -> GapA2`.

Case split of GapA2 (N = 15, Case A; every n with all prime factors < 7 and 15 | n is n = 2^i 3^j 5^k, j, k >= 1) by (i, j, k):
Proved in Lean (all `#print axioms` standard):
  15 !| n                                                : GA2OBase.fifteen_dvd
  n = 15                                                  : GA2OBase.gapA2_n15
  i >= 3 (any j, k >= 1)                                  : GA2NSlice.gapA2_slice_i3   (Theorem A)
  i in {0, 2}, k = 1, j >= 2                              : GA2PH.gapA2_slice_i02      (Theorems C and B)
  i = 1, k = 1, j >= 2, every entry prime to 5 prime to 3 : GA2QD5.gapA2_slice_D       (Proposition D)
  n = 75, n = 90                                          : GA2OFin2.gapA2_n75 / _n90 (single values)
Not covered (the residual hypothesis `GapA2Residual2`, quantifying exactly over these cases):
  (R-30/60) j = k = 1, i in {1, 2}                                       n = 30, 60
  (R-D3)    i = 1, k = 1, j >= 2, some entry divisible by 3 and not by 5  (n = 90 itself is closed above)
  (R-K)     k >= 2, i <= 2, j >= 1, (i,j,k) != (0,1,2)                    Props K-a (i = 2), K-b (i = 0), K-c (i = 1)
No new mathematics beyond the cited pieces; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QA
import Erdos634.Draft.GA2QD5
import Erdos634.Draft.GA2QD6

namespace Erdos634.GA2QF

open Erdos634.Geometry Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.GA2Q (ResidualIJK smooth_rep)

/-- **The residual hypothesis, refined by Proposition D.** -/
def GapA2Residual2 : Prop :=
  ∀ (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (i j k : ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ t, D.model.angleAt t = a t * Real.pi / n) →
    n = 2 ^ i * 3 ^ j * 5 ^ k → ResidualIJK i j k →
    ((i = 1 ∧ k = 1 ∧ 2 ≤ j) → ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t) → False

theorem gapA2_of_residual2 (R : GapA2Residual2) : Erdos634.CaseA.R0c15.GapA2 := by
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
    · by_cases hD3 : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t
      · exact R D n a i j k hn hgcd ha e hR (fun _ => hD3)
      · -- no entry prime to 5 is divisible by 3
        have h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t := by
          intro t h5 h3t
          exact hD3 ⟨t, h5, h3t⟩
        by_cases hD : i = 1 ∧ k = 1 ∧ 2 ≤ j
        · obtain ⟨rfl, rfl, hj2⟩ := hD
          exact Erdos634.GA2QD5.gapA2_slice_D D n a hn hgcd ha ⟨j, hj2, by rw [e]; ring⟩ h3
        · exact R D n a i j k hn hgcd ha e hR (fun h => absurd h hD)
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

/-- the refined residual is implied by the previous one's hypothesis shape (GapA2Residual2 is weaker as a hypothesis) -/
theorem residual2_of_residual (R : Erdos634.GA2Q.GapA2Residual) : GapA2Residual2 :=
  fun D n a i j k hn hgcd ha e hR _ => R D n a i j k hn hgcd ha e hR

/-- Exhibit that the refined residual domain is nonempty arithmetically: n = 30, 60, 270 with an entry divisible by 3, n = 25 * 2 ... -/
theorem residual2_domain_witnesses :
    ResidualIJK 1 1 1 ∧ ResidualIJK 2 1 1 ∧ ResidualIJK 1 3 1 ∧ ResidualIJK 0 1 3 ∧ ResidualIJK 2 2 2 ∧ ResidualIJK 1 1 2 :=
  ⟨by unfold ResidualIJK; decide, by unfold ResidualIJK; decide, by unfold ResidualIJK; decide,
   by unfold ResidualIJK; decide, by unfold ResidualIJK; decide, by unfold ResidualIJK; decide⟩

/-- the (R-D3) tile exists arithmetically: n = 270, tile (1, 2, 267) has the entry 267 = 3 * 89 divisible by 3 and not by 5 -/
theorem r_d3_tile_example : (1 + 2 + 267 = 2 * 3 ^ 3 * 5) ∧ Nat.gcd 1 (Nat.gcd 2 267) = 1 ∧ ¬ 5 ∣ 267 ∧ 3 ∣ 267 := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩


#print axioms Erdos634.GA2QF.gapA2_of_residual2
#print axioms Erdos634.GA2QF.residual2_of_residual
#print axioms Erdos634.GA2QF.residual2_domain_witnesses
#print axioms Erdos634.GA2QF.r_d3_tile_example

/-! ### the five named parts of the residual -/

/-- common shape of a case of GapA2 over a set of exponent triples -/
def GapA2On (Φ : ℕ → ℕ → ℕ → (Fin 3 → ℕ) → Prop) : Prop :=
  ∀ (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (i j k : ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ t, D.model.angleAt t = a t * Real.pi / n) →
    n = 2 ^ i * 3 ^ j * 5 ^ k → Φ i j k a → False

/-- n = 30, 60 (K2, K3 of GA2Y_NOTES) -/
def PartN3060 : Prop := GapA2On (fun i j k _ => j = 1 ∧ k = 1 ∧ (i = 1 ∨ i = 2))
/-- i = 1, k = 1, j >= 2, an entry divisible by 3 and not by 5, j = 2 excluded (n = 90 is a closed single value) -/
def PartD3 : Prop := GapA2On (fun i j k a => i = 1 ∧ k = 1 ∧ 2 ≤ j ∧ (i, j, k) ≠ (1, 2, 1) ∧ ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)
/-- Prop K-a: i = 2, k >= 2, j >= 1 -/
def PartKa : Prop := GapA2On (fun i j k _ => i = 2 ∧ 2 ≤ k ∧ 1 ≤ j)
/-- Prop K-b: i = 0, k >= 2, j >= 1, n = 75 excluded (closed single value) -/
def PartKb : Prop := GapA2On (fun i j k _ => i = 0 ∧ 2 ≤ k ∧ 1 ≤ j ∧ (i, j, k) ≠ (0, 1, 2))
/-- Prop K-c: i = 1, k >= 2, j >= 1 -/
def PartKc : Prop := GapA2On (fun i j k _ => i = 1 ∧ 2 ≤ k ∧ 1 ≤ j)

theorem residual2_of_parts (h1 : PartN3060) (h2 : PartD3) (h3 : PartKa) (h4 : PartKb) (h5 : PartKc) :
    GapA2Residual2 := by
  intro D n a i j k hn hgcd ha e hR hD3
  unfold ResidualIJK at hR
  obtain ⟨hj, hk, hi, hne1, hne2, hcase⟩ := hR
  rcases hcase with ⟨hj1, hk1, hi12⟩ | ⟨hi1, hk1, hj2⟩ | hk2
  · exact h1 D n a i j k hn hgcd ha e ⟨hj1, hk1, hi12⟩
  · exact h2 D n a i j k hn hgcd ha e ⟨hi1, hk1, hj2, hne2, hD3 ⟨hi1, hk1, hj2⟩⟩
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact h4 D n a _ j k hn hgcd ha e ⟨rfl, hk2, hj, hne1⟩
    · exact h5 D n a _ j k hn hgcd ha e ⟨rfl, hk2, hj⟩
    · exact h3 D n a _ j k hn hgcd ha e ⟨rfl, hk2, hj⟩

theorem gapA2_of_parts (h1 : PartN3060) (h2 : PartD3) (h3 : PartKa) (h4 : PartKb) (h5 : PartKc) :
    Erdos634.CaseA.R0c15.GapA2 :=
  gapA2_of_residual2 (residual2_of_parts h1 h2 h3 h4 h5)

end Erdos634.GA2QF

#print axioms Erdos634.GA2QF.residual2_of_parts
#print axioms Erdos634.GA2QF.gapA2_of_parts
