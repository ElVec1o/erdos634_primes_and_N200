/- GA2OC: row-wise re-chunking of `LemmaS.allCert`.  `allCert n` is the conjunction over a0 < n of `rowOK n a0`;
a row-range check `rowsOK n lo len` is one kernel `decide` of bounded size, and `allCert_of_chunks` reassembles `allCert n = true`. -/
import Mathlib
import Erdos634.Draft.GA2OBase

namespace Erdos634.GA2OC

open Erdos634.LemmaS

def rowOK (n a0 : ℕ) : Bool :=
  (List.range n).all fun a1 =>
    if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then
      cert n a0 a1 (n - a0 - a1) else true

def rowsOK (n lo len : ℕ) : Bool := (List.range' lo len).all (rowOK n)

theorem allCert_eq (n : ℕ) : allCert n = (List.range n).all (rowOK n) := rfl

/-- Reassembly: rows `[0, n)` covered by finitely many verified chunks. -/
theorem allCert_of_rows (n : ℕ) (h : ∀ a0, a0 < n → rowOK n a0 = true) : allCert n = true := by
  rw [allCert_eq]; simp only [List.all_eq_true, List.mem_range]; exact h

theorem rowOK_of_rowsOK {n lo len : ℕ} (h : rowsOK n lo len = true) {a0 : ℕ} (h1 : lo ≤ a0)
    (h2 : a0 < lo + len) : rowOK n a0 = true := by
  unfold rowsOK at h
  simp only [List.all_eq_true, List.mem_range'_1] at h
  exact h a0 ⟨h1, h2⟩

theorem rowsOK_add (n lo l1 l2 : ℕ) (h1 : rowsOK n lo l1 = true) (h2 : rowsOK n (lo + l1) l2 = true) :
    rowsOK n lo (l1 + l2) = true := by
  unfold rowsOK at *
  simp only [List.all_eq_true, List.mem_range'_1] at *
  intro a ha
  by_cases hl : a < lo + l1
  · exact h1 a ⟨ha.1, hl⟩
  · exact h2 a ⟨by omega, by omega⟩

theorem rowsOK_zero (n lo : ℕ) : rowsOK n lo 0 = true := rfl

theorem allCert_of_rows_all (n : ℕ) (h : rowsOK n 0 n = true) : allCert n = true :=
  allCert_of_rows n fun a0 ha => rowOK_of_rowsOK h (Nat.zero_le _) (by omega)

end Erdos634.GA2OC
