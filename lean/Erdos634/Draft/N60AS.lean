/-
N60A-S: row slicing of the per-tile kernel check `chkTileF` (outer index `A`), so that heavy tiles can be checked in several kernel modules
(constant-60 near-equilateral tiles exceed 9 GB in one `decide +kernel`).  `rowOK` is one value of the outer index; `rowsOK a0 len` a block of rows;
`chkTileF_of_rows2/3/4` assemble.  Pure Bool/list lemmas; no sorry / native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2RK

namespace Erdos634.N60A

open Erdos634.GA2R

def rowOK (fac : ℕ) (sl sh : ℕ → ℕ) (n t1 t2 t3 A : ℕ) : Bool :=
  (List.range n).all fun B =>
    !(decide (1 ≤ A ∧ 1 ≤ B ∧ A + B < n)) || tgtOkF fac sl sh t1 t2 t3 A B (n - A - B)

def rowsOK (fac : ℕ) (sl sh : ℕ → ℕ) (n t1 t2 t3 a0 len : ℕ) : Bool :=
  (List.range' a0 len).all fun A => rowOK fac sl sh n t1 t2 t3 A

theorem chkTileF_of_rowOK (fac : ℕ) (sl sh : ℕ → ℕ) (n t1 t2 t3 : ℕ)
    (h : ∀ A < n, rowOK fac sl sh n t1 t2 t3 A = true) : chkTileF fac sl sh n t1 t2 t3 = true := by
  unfold chkTileF
  rw [List.all_eq_true]
  intro A hA
  exact h A (List.mem_range.mp hA)

theorem rowOK_of_rowsOK {fac : ℕ} {sl sh : ℕ → ℕ} {n t1 t2 t3 a0 len : ℕ}
    (h : rowsOK fac sl sh n t1 t2 t3 a0 len = true) {A : ℕ} (h1 : a0 ≤ A) (h2 : A < a0 + len) :
    rowOK fac sl sh n t1 t2 t3 A = true := by
  unfold rowsOK at h
  rw [List.all_eq_true] at h
  exact h A (List.mem_range'_1.mpr ⟨h1, h2⟩)

theorem chkTileF_of_rows2 (fac : ℕ) (sl sh : ℕ → ℕ) (n t1 t2 t3 k1 : ℕ) (hk1 : k1 ≤ n)
    (h1 : rowsOK fac sl sh n t1 t2 t3 0 k1 = true) (h2 : rowsOK fac sl sh n t1 t2 t3 k1 (n - k1) = true) :
    chkTileF fac sl sh n t1 t2 t3 = true := by
  apply chkTileF_of_rowOK
  intro A hA
  by_cases hc : A < k1
  · exact rowOK_of_rowsOK h1 (by omega) (by omega)
  · exact rowOK_of_rowsOK h2 (by omega) (by omega)

theorem chkTileF_of_rows3 (fac : ℕ) (sl sh : ℕ → ℕ) (n t1 t2 t3 k1 k2 : ℕ) (hk1 : k1 ≤ k2) (hk2 : k2 ≤ n)
    (h1 : rowsOK fac sl sh n t1 t2 t3 0 k1 = true) (h2 : rowsOK fac sl sh n t1 t2 t3 k1 (k2 - k1) = true)
    (h3 : rowsOK fac sl sh n t1 t2 t3 k2 (n - k2) = true) :
    chkTileF fac sl sh n t1 t2 t3 = true := by
  apply chkTileF_of_rowOK
  intro A hA
  by_cases hc : A < k1
  · exact rowOK_of_rowsOK h1 (by omega) (by omega)
  by_cases hc2 : A < k2
  · exact rowOK_of_rowsOK h2 (by omega) (by omega)
  · exact rowOK_of_rowsOK h3 (by omega) (by omega)

theorem chkTileF_of_rows4 (fac : ℕ) (sl sh : ℕ → ℕ) (n t1 t2 t3 k1 k2 k3 : ℕ) (hk1 : k1 ≤ k2) (hk2 : k2 ≤ k3) (hk3 : k3 ≤ n)
    (h1 : rowsOK fac sl sh n t1 t2 t3 0 k1 = true) (h2 : rowsOK fac sl sh n t1 t2 t3 k1 (k2 - k1) = true)
    (h3 : rowsOK fac sl sh n t1 t2 t3 k2 (k3 - k2) = true) (h4 : rowsOK fac sl sh n t1 t2 t3 k3 (n - k3) = true) :
    chkTileF fac sl sh n t1 t2 t3 = true := by
  apply chkTileF_of_rowOK
  intro A hA
  by_cases hc : A < k1
  · exact rowOK_of_rowsOK h1 (by omega) (by omega)
  by_cases hc2 : A < k2
  · exact rowOK_of_rowsOK h2 (by omega) (by omega)
  by_cases hc3 : A < k3
  · exact rowOK_of_rowsOK h3 (by omega) (by omega)
  · exact rowOK_of_rowsOK h4 (by omega) (by omega)

/-- control: the slice decomposition agrees with the original checker on a small instance (n = 30, tile (28,1,1)). -/
theorem control_rows_agree :
    chkTileF 30 (slc 2) (shc 2) 30 28 1 1 = (rowsOK 30 (slc 2) (shc 2) 30 28 1 1 0 30) := by
  decide +kernel

#print axioms chkTileF_of_rows2
#print axioms chkTileF_of_rows3
#print axioms chkTileF_of_rows4
#print axioms control_rows_agree

end Erdos634.N60A
