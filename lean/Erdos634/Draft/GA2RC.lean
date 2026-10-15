/-
GA2R-C: from `chkTile` to "no tile": the all-tiles checker `chkAllX` / `chkAll` and the combinatorial reduction
(sorting a tile by sine, permutation invariance of the identity), still abstract in the table `sl sh`.
`no_tile_of_chkAll`: if `chkAll n sl sh = true` and the table (T) holds, then for every `a : Fin 3 -> N` with a_k >= 1,
sum = n, gcd = 1, every ordered target (A,B,C) (>= 1, sum n) and every m in N^3, the identity
  (sum m_k sin(a_k pi/n))^2 sin(B pi/n) sin(C pi/n) = 15 sin(A pi/n) prod_k sin(a_k pi/n)
is false.  No sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2RB

namespace Erdos634.GA2R

open Finset

/-- sine-size key: smaller `kk` = larger sine (`kk u = max(u, n-u)`) -/
def kk (n u : ℕ) : ℕ := max u (n - u)

theorem chkTile_sound {n : ℕ} {sl sh : ℕ → ℕ} (htab : Tab n sl sh) {t1 t2 t3 : ℕ} (h1 : t1 ≤ n) (h2 : t2 ≤ n)
    (h3 : t3 ≤ n) (hchk : chkTile sl sh n t1 t2 t3 = true) {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hs : A + B + C = n) (m1 m2 m3 : ℕ)
    (hid : ((m1 : ℝ) * Real.sin (t1 * Real.pi / n) + m2 * Real.sin (t2 * Real.pi / n) +
        m3 * Real.sin (t3 * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
      = 15 * Real.sin (A * Real.pi / n) * Real.sin (t1 * Real.pi / n) * Real.sin (t2 * Real.pi / n) *
        Real.sin (t3 * Real.pi / n)) : False := by
  unfold chkTile at hchk
  rw [List.all_eq_true] at hchk
  have hA' := hchk A (List.mem_range.mpr (by omega))
  rw [List.all_eq_true] at hA'
  have hB' := hA' B (List.mem_range.mpr (by omega))
  have hcond : decide (1 ≤ A ∧ 1 ≤ B ∧ A + B < n) = true := by simp; omega
  rw [hcond] at hB'
  simp only [Bool.not_true, Bool.false_or] at hB'
  have hC' : n - A - B = C := by omega
  rw [hC'] at hB'
  exact tgtOk_sound n sl sh htab h1 h2 h3 (by omega) (by omega) (by omega) hB' m1 m2 m3 hid

/-- the per-tile condition run by `chkAll` : triples sorted by `kk`, sum n, entries >= 1, gcd 1 -/
def tileCond (n x y : ℕ) : Bool :=
  decide (1 ≤ x ∧ 1 ≤ y ∧ x + y < n ∧ kk n x ≤ kk n y ∧ kk n y ≤ kk n (n - x - y) ∧
    Nat.gcd x (Nat.gcd y (n - x - y)) = 1)

/-- all tiles with first entry `x` -/
def chkAllX (sl sh : ℕ → ℕ) (n x : ℕ) : Bool :=
  (List.range n).all fun y => !(tileCond n x y) || chkTile sl sh n x y (n - x - y)

def chkAll (sl sh : ℕ → ℕ) (n : ℕ) : Bool := (List.range n).all fun x => chkAllX sl sh n x

theorem chkAll_of_chunks {sl sh : ℕ → ℕ} {n : ℕ} (h : ∀ x < n, chkAllX sl sh n x = true) :
    chkAll sl sh n = true := by
  unfold chkAll; rw [List.all_eq_true]; intro x hx; exact h x (List.mem_range.mp hx)

/-- identity, in `Fin 3` form (as produced by `star`) -/
def IdFin (n : ℕ) (a : Fin 3 → ℕ) (A B C : ℕ) (m : Fin 3 → ℕ) : Prop :=
  (∑ k, (m k : ℝ) * Real.sin (a k * Real.pi / n)) ^ 2 * Real.sin (B * Real.pi / n) * Real.sin (C * Real.pi / n)
    = 15 * Real.sin (A * Real.pi / n) * ∏ k, Real.sin (a k * Real.pi / n)

theorem no_tile_of_chkAll {n : ℕ} {sl sh : ℕ → ℕ} (hn : 0 < n) (htab : Tab n sl sh)
    (hchk : chkAll sl sh n = true) (a : Fin 3 → ℕ) (ha1 : ∀ k, 1 ≤ a k) (hsum : ∑ k, a k = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C)
    (hs : A + B + C = n) (m : Fin 3 → ℕ) (hid : IdFin n a A B C m) : False := by
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
  unfold chkAll at hc
  rw [List.all_eq_true] at hc
  have hc1 := hc x (List.mem_range.mpr hxn)
  unfold chkAllX at hc1
  rw [List.all_eq_true] at hc1
  have hc2 := hc1 y (List.mem_range.mpr hyn)
  have hcond : tileCond n x y = true := by
    unfold tileCond
    simp only [decide_eq_true_eq]
    refine ⟨hx1, hy1, by omega, k01, by rw [← hzn]; exact k12, by rw [← hzn]; exact hg⟩
  rw [hcond] at hc2
  simp only [Bool.not_true, Bool.false_or] at hc2
  rw [← hzn] at hc2
  refine chkTile_sound htab (by omega) (by omega) (by omega) hc2 hA hB hC hs (m (σ 0)) (m (σ 1)) (m (σ 2)) ?_
  unfold IdFin at hid
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
  rw [show (15 : ℝ) * Real.sin (A * Real.pi / n) * Real.sin (x * Real.pi / n) * Real.sin (y * Real.pi / n) *
      Real.sin (z * Real.pi / n) = 15 * Real.sin (A * Real.pi / n) * (Real.sin (x * Real.pi / n) *
      Real.sin (y * Real.pi / n) * Real.sin (z * Real.pi / n)) by ring, e2]
  exact hid

#print axioms no_tile_of_chkAll

end Erdos634.GA2R
