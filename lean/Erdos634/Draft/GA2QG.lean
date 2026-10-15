/-
Assembly (v3): `GapA2Residual3` and `gapA2_of_residual3 : GapA2Residual3 -> GapA2`; `gapA2_of_parts3`.

Case split of GapA2 (N = 15, Case A; every n with all prime factors < 7 and 15 | n is n = 2^i 3^j 5^k, j, k >= 1) by (i, j, k):
Proved in Lean (all `#print axioms` standard):
  15 !| n                                                              : GA2OBase.fifteen_dvd
  n = 15                                                                : GA2OBase.gapA2_n15
  i >= 3 (any j, k >= 1)                                                : GA2NSlice.gapA2_slice_i3     (Theorem A)
  i in {0, 2}, k = 1, j >= 2                                            : GA2PH.gapA2_slice_i02        (Theorems C and B)
  i = 1, k = 1, j >= 2, every entry prime to 5 prime to 3               : GA2QD5.gapA2_slice_D         (Proposition D)
  i = 1, k >= 2, j >= 1, every entry prime to 5 prime to 3              : GA2QK5.gapA2_slice_K1        (Prop K-c, no-3 part)
  i = 0, k >= 2, j >= 1, every entry prime to 5 prime to 3              : GA2QK5.gapA2_slice_K0        (Prop K-b, no-3 part)
  n = 75, n = 90                                                        : GA2OFin2.gapA2_n75 / _n90 (single values)
Not covered (the residual hypothesis `GapA2Residual3`, quantifying exactly over these cases):
  (R-30/60) j = k = 1, i in {1, 2}                                      n = 30, 60
  (R-3)     i in {0, 1}, (i = 1 and (k = 1, j >= 2) or k >= 2) or (i = 0 and k >= 2): tiles with an entry divisible by 3 and not by 5
            (for i = 1, k = 1 this is the case not covered by Prop D; the fixed-eta3 K0 argument of Prop K-b/K-c)
  (R-Ka)    i = 2, k >= 2, j >= 1                                       Prop K-a
No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2QA
import Erdos634.Draft.GA2QD5
import Erdos634.Draft.GA2QK5
import Erdos634.Draft.GA2QK6

namespace Erdos634.GA2QG

open Erdos634.Geometry Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.GA2Q (ResidualIJK smooth_rep)

/-- the extra hypothesis on the tile for the rows where a "no entry of I divisible by 3" slice exists -/
def Has3 (i j k : ℕ) (a : Fin 3 → ℕ) : Prop :=
  ((i = 1 ∧ ((k = 1 ∧ 2 ≤ j) ∨ 2 ≤ k)) ∨ (i = 0 ∧ 2 ≤ k)) → ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t

/-- **The residual hypothesis, refined by Proposition D and the no-3 parts of Props K-b, K-c.** -/
def GapA2Residual3 : Prop :=
  ∀ (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (i j k : ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ t, D.model.angleAt t = a t * Real.pi / n) →
    n = 2 ^ i * 3 ^ j * 5 ^ k → ResidualIJK i j k → Has3 i j k a → False

theorem gapA2_of_residual3 (R : GapA2Residual3) : Erdos634.CaseA.R0c15.GapA2 := by
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
      · have h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t := by
          intro t h5 h3t
          exact hD3 ⟨t, h5, h3t⟩
        by_cases hc : (i = 1 ∧ ((k = 1 ∧ 2 ≤ j) ∨ 2 ≤ k)) ∨ (i = 0 ∧ 2 ≤ k)
        · rcases hc with ⟨hi1, hkj⟩ | ⟨hi0, hk2⟩
          · subst hi1
            rcases hkj with ⟨rfl, hj2⟩ | hk2
            · exact Erdos634.GA2QD5.gapA2_slice_D D n a hn hgcd ha ⟨j, hj2, by rw [e]; ring⟩ h3
            · exact Erdos634.GA2QK5.gapA2_slice_K1 D n a hn hgcd ha k j hk hj (Or.inl hk2)
                (by rw [e]; ring) h3
          · subst hi0
            exact Erdos634.GA2QK5.gapA2_slice_K0 D n a hn hgcd ha k j hk hj (by rw [e]; ring) h3
        · exact R D n a i j k hn hgcd ha e hR (fun h => absurd h hc)
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

/-! ### the named parts of the remaining residual -/

/-- common shape of a case of GapA2 over a set of exponent triples (and tiles) -/
def GapA2On (Φ : ℕ → ℕ → ℕ → (Fin 3 → ℕ) → Prop) : Prop :=
  ∀ (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (i j k : ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ t, D.model.angleAt t = a t * Real.pi / n) →
    n = 2 ^ i * 3 ^ j * 5 ^ k → Φ i j k a → False

/-- n = 30, 60 (K2, K3 of GA2Y_NOTES) -/
def PartN3060 : Prop := GapA2On (fun i j k _ => j = 1 ∧ k = 1 ∧ (i = 1 ∨ i = 2))
/-- i = 1, k = 1, j >= 2, an entry divisible by 3 and not by 5; (1,2,1) = n = 90 is a closed single value -/
def PartD3 : Prop := GapA2On (fun i j k a => i = 1 ∧ k = 1 ∧ 2 ≤ j ∧ (i, j, k) ≠ (1, 2, 1) ∧ ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)
/-- Prop K-a: i = 2, k >= 2, j >= 1 -/
def PartKa : Prop := GapA2On (fun i j k _ => i = 2 ∧ 2 ≤ k ∧ 1 ≤ j)
/-- Prop K-b, tiles with an entry divisible by 3 and not by 5: i = 0, k >= 2, j >= 1 (n = 75 excluded: closed single value) -/
def PartKb3 : Prop := GapA2On (fun i j k a => i = 0 ∧ 2 ≤ k ∧ 1 ≤ j ∧ (i, j, k) ≠ (0, 1, 2) ∧ ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)
/-- Prop K-c, tiles with an entry divisible by 3 and not by 5: i = 1, k >= 2, j >= 1 -/
def PartKc3 : Prop := GapA2On (fun i j k a => i = 1 ∧ 2 ≤ k ∧ 1 ≤ j ∧ ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t)

theorem residual3_of_parts (h1 : PartN3060) (h2 : PartD3) (h3 : PartKa) (h4 : PartKb3) (h5 : PartKc3) :
    GapA2Residual3 := by
  intro D n a i j k hn hgcd ha e hR hH
  unfold ResidualIJK at hR
  obtain ⟨hj, hk, hi, hne1, hne2, hcase⟩ := hR
  rcases hcase with ⟨hj1, hk1, hi12⟩ | ⟨hi1, hk1, hj2⟩ | hk2
  · exact h1 D n a i j k hn hgcd ha e ⟨hj1, hk1, hi12⟩
  · exact h2 D n a i j k hn hgcd ha e ⟨hi1, hk1, hj2, hne2, hH (Or.inl ⟨hi1, Or.inl ⟨hk1, hj2⟩⟩)⟩
  · have : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl | rfl
    · exact h4 D n a _ j k hn hgcd ha e ⟨rfl, hk2, hj, hne1, hH (Or.inr ⟨rfl, hk2⟩)⟩
    · exact h5 D n a _ j k hn hgcd ha e ⟨rfl, hk2, hj, hH (Or.inl ⟨rfl, Or.inr hk2⟩)⟩
    · exact h3 D n a _ j k hn hgcd ha e ⟨rfl, hk2, hj⟩

theorem gapA2_of_parts3 (h1 : PartN3060) (h2 : PartD3) (h3 : PartKa) (h4 : PartKb3) (h5 : PartKc3) :
    Erdos634.CaseA.R0c15.GapA2 :=
  gapA2_of_residual3 (residual3_of_parts h1 h2 h3 h4 h5)

/-- the weaker residuals imply this one's hypothesis shape (GapA2Residual3 is a weaker hypothesis than GapA2Residual) -/
theorem residual3_of_residual (R : Erdos634.GA2Q.GapA2Residual) : GapA2Residual3 :=
  fun D n a i j k hn hgcd ha e hR _ => R D n a i j k hn hgcd ha e hR

end Erdos634.GA2QG

#print axioms Erdos634.GA2QG.gapA2_of_residual3
#print axioms Erdos634.GA2QG.residual3_of_parts
#print axioms Erdos634.GA2QG.gapA2_of_parts3
#print axioms Erdos634.GA2QG.residual3_of_residual
