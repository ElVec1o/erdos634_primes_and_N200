/-
N30K-C: constant-`fac` versions of GA2RC: `chkAllF`, `chkTileF_sound`, `no_tile_of_chkAllF` (reuses `kk`, `tileCond`, `Tab` of GA2RB/GA2RC),
and (section 2) the consumer at N = 30: `identity30` from `CaseALemmaVDissection.star` and `no_dissection30_n`.  No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.N30KB
import Erdos634.Draft.GA2RD0
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseAR0c

namespace Erdos634.N30K

open Finset Erdos634.GA2R

theorem chkTileF_sound (fac : ℕ) {n : ℕ} {sl sh : ℕ → ℕ} (htab : Tab n sl sh) {t1 t2 t3 : ℕ} (h1 : t1 ≤ n) (h2 : t2 ≤ n)
    (h3 : t3 ≤ n) (hchk : chkTileF fac sl sh n t1 t2 t3 = true) {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hs : A + B + C = n) (m1 m2 m3 : ℕ)
    (hid : ((m1 : ℝ) * Real.sin (t1 * Real.pi / n) + m2 * Real.sin (t2 * Real.pi / n) +
        m3 * Real.sin (t3 * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
      = (fac : ℝ) * Real.sin (A * Real.pi / n) * Real.sin (t1 * Real.pi / n) * Real.sin (t2 * Real.pi / n) *
        Real.sin (t3 * Real.pi / n)) : False := by
  unfold chkTileF at hchk
  rw [List.all_eq_true] at hchk
  have hA' := hchk A (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at hA'
  have hB' := hA' B (List.mem_range.mpr (by omega))
  have hcond : decide (1 ≤ A ∧ 1 ≤ B ∧ A + B < n) = true := by simp; omega
  rw [hcond] at hB'
  simp only [Bool.not_true, Bool.false_or] at hB'
  have hC' : n - A - B = C := by omega
  rw [hC'] at hB'
  exact tgtOkF_sound n sl sh fac htab h1 h2 h3 (by omega) (by omega) (by omega) hB' m1 m2 m3 hid

/-- all tiles with first entry `x` -/
def chkAllXF (fac : ℕ) (sl sh : ℕ → ℕ) (n x : ℕ) : Bool :=
  (List.range n).all fun y => !(tileCond n x y) || chkTileF fac sl sh n x y (n - x - y)

def chkAllF (fac : ℕ) (sl sh : ℕ → ℕ) (n : ℕ) : Bool := (List.range n).all fun x => chkAllXF fac sl sh n x

/-- identity, in `Fin 3` form (as produced by `star`) -/
def IdFinF (fac : ℕ) (n : ℕ) (a : Fin 3 → ℕ) (A B C : ℕ) (m : Fin 3 → ℕ) : Prop :=
  (∑ k, (m k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
    = (fac : ℝ) * Real.sin (A * Real.pi / n) * ∏ k, Real.sin (a k * Real.pi / n)

theorem no_tile_of_chkAllF (fac : ℕ) {n : ℕ} {sl sh : ℕ → ℕ} (hn : 0 < n) (htab : Tab n sl sh)
    (hchk : chkAllF fac sl sh n = true) (a : Fin 3 → ℕ) (ha1 : ∀ k, 1 ≤ a k) (hsum : ∑ k, a k = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hs : A + B + C = n) (m : Fin 3 → ℕ) (hid : IdFinF fac n a A B C m) : False := by
  set σ := Tuple.sort (fun k => kk n (a k)) with hσ
  have hmono : Monotone ((fun k => kk n (a k)) ∘ σ) := Tuple.monotone_sort _
  set x := a (σ 0) with hx
  set y := a (σ 1) with hy
  set z := a (σ 2) with hz
  have hsum' : x + y + z = n := by
    have := Equiv.sum_comp σ a
    rw [Fin.sum_univ_three, Fin.sum_univ_three] at this
    rw [Fin.sum_univ_three] at hsum
    omega
  have hx1 : 1 ≤ x := ha1 _
  have hy1 : 1 ≤ y := ha1 _
  have hz1 : 1 ≤ z := ha1 _
  have k01 : kk n x ≤ kk n y := hmono (show (0 : Fin 3) ≤ 1 by decide)
  have k12 : kk n y ≤ kk n z := hmono (show (1 : Fin 3) ≤ 2 by decide)
  have hzn : z = n - x - y := by omega
  have hg : Nat.gcd x (Nat.gcd y z) = 1 := by
    have hd : ∀ k : Fin 3, Nat.gcd x (Nat.gcd y z) ∣ a k := by
      intro k
      have hk : ∃ j, σ j = k := ⟨σ.symm k, by simp⟩
      obtain ⟨j, rfl⟩ := hk
      fin_cases j
      · exact Nat.gcd_dvd_left _ _
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
      · exact (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
    have : Nat.gcd x (Nat.gcd y z) ∣ Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) :=
      Nat.dvd_gcd (hd 0) (Nat.dvd_gcd (hd 1) (hd 2))
    rw [hgcd] at this
    exact Nat.dvd_one.mp this
  have hxn : x < n := by omega
  have hyn : y < n := by omega
  have hc := hchk
  unfold chkAllF at hc
  rw [List.all_eq_true] at hc
  have hc1 := hc x (List.mem_range.mpr hxn)
  unfold chkAllXF at hc1
  rw [List.all_eq_true] at hc1
  have hc2 := hc1 y (List.mem_range.mpr hyn)
  have hcond : tileCond n x y = true := by
    unfold tileCond
    simp only [decide_eq_true_eq]
    refine ⟨hx1, hy1, by omega, k01, by rw [← hzn]; exact k12, by rw [← hzn]; exact hg⟩
  rw [hcond] at hc2
  simp only [Bool.not_true, Bool.false_or] at hc2
  rw [← hzn] at hc2
  refine chkTileF_sound fac htab (by omega) (by omega) (by omega) hc2 hA hB hC hs (m (σ 0)) (m (σ 1)) (m (σ 2)) ?_
  unfold IdFinF at hid
  rw [Fin.sum_univ_three] at hid
  have e1 := Equiv.sum_comp σ (fun k => (m k : ℝ) * Real.sin (a k * Real.pi / n))
  have e2 := Equiv.prod_comp σ (fun k => Real.sin (a k * Real.pi / n))
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at e1
  rw [Fin.prod_univ_three, Fin.prod_univ_three] at e2
  rw [Fin.prod_univ_three] at hid
  have : ((m (σ 0) : ℝ) * Real.sin (x * Real.pi / n) + m (σ 1) * Real.sin (y * Real.pi / n) +
      m (σ 2) * Real.sin (z * Real.pi / n)) = (m 0 : ℝ) * Real.sin (a 0 * Real.pi / n) +
      m 1 * Real.sin (a 1 * Real.pi / n) + m 2 * Real.sin (a 2 * Real.pi / n) := e1
  rw [this]
  rw [show (fac : ℝ) * Real.sin (A * Real.pi / n) * Real.sin (x * Real.pi / n) * Real.sin (y * Real.pi / n) *
      Real.sin (z * Real.pi / n) = (fac : ℝ) * Real.sin (A * Real.pi / n) * (Real.sin (x * Real.pi / n) *
      Real.sin (y * Real.pi / n) * Real.sin (z * Real.pi / n)) by ring, e2]
  exact hid

#print axioms no_tile_of_chkAllF

open Erdos634.Geometry Erdos634.Geometry.CaseA.LemmaV

/-- **The identity with the constant 30.** -/
theorem identity30 (D : CongruentDissection 30) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    (∀ k, 1 ≤ a k) ∧ ∑ k, a k = n ∧
    ∃ (b c : Fin 3 → ℕ), (∀ k, 1 ≤ b k) ∧ ∑ k, b k = n ∧ IdFinF 30 n a (b 0) (b 1) (b 2) c := by
  choose b hb using target_angle_nat D hn a ha
  obtain ⟨c, hc⟩ := star D
  refine ⟨fun k => (nat_bounds hn (ha k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn ha, b, c,
    fun k => (nat_bounds hn (hb k) (angle_pos _ k) (angle_lt_pi _ k)).1,
    Erdos634.CaseA.R0c.sum_of_angles hn hb, ?_⟩
  simp only [ha, hb] at hc
  unfold IdFinF
  rw [Fin.prod_univ_three]
  push_cast at hc
  linear_combination (-1 : ℝ) * hc

theorem no_dissection30_n {n : ℕ} {sl sh : ℕ → ℕ} (hn : 0 < n) (htab : Tab n sl sh)
    (hchk : chkAllF 30 sl sh n = true) (D : CongruentDissection 30) (a : Fin 3 → ℕ)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) :
    False := by
  obtain ⟨ha1, hsum, b, c, hb1, hbs, hid⟩ := identity30 D hn a ha
  have hbs' := hbs
  rw [Fin.sum_univ_three] at hbs'
  exact no_tile_of_chkAllF 30 hn htab hchk a ha1 hsum hgcd (hb1 0) (hb1 1) (hb1 2) hbs' c hid

#print axioms identity30
#print axioms no_dissection30_n

end Erdos634.N30K
