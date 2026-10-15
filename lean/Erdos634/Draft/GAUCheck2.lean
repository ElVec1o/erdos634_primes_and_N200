/-
Draft/GAUCheck2.lean -- tile tables given by PARTS of rows (`lo ≤ B < hi`), for the level `n = 60`, where a whole row
in one kernel `decide` needs about 9 GB.

Composite-N statement; not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.GAUCheck

namespace Erdos634.Draft.GAU

/-- part of a row: the targets `(A, B, n − A − B)` with `lo ≤ B < hi`, certificates in order from `B = lo` -/
def chkRowR (d n : ℕ) (red : List (List ℤ)) (a : Fin 3 → ℕ) (A lo hi : ℕ) (row : List Cert) : Bool :=
  (List.range (hi - lo)).all fun k =>
    !(decide (1 ≤ lo + k ∧ A + (lo + k) < n)) ||
      chkCase d n red a A (lo + k) (n - A - (lo + k)) (row.getD k (Cert.I []))

/-- **Soundness of a table given by parts of rows.** -/
theorem chkRowsR_sound {n : ℕ} (hn : 0 < n) {red : List (List ℤ)} (hredlen : red.length = n)
    (hred : ∀ e, e < n → zx n ^ e = ev (zx n) (red.getD e []) ∧ (red.getD e []).length ≤ Nat.totient (2 * n))
    {d : ℕ} (hd : 0 < d) {a : Fin 3 → ℕ} (ha0 : ∀ k, 0 < a k) (han : ∀ k, a k < n)
    (h : ∀ A B, 1 ≤ A → 1 ≤ B → A + B < n →
      ∃ lo hi row, lo ≤ B ∧ B < hi ∧ chkRowR d n red a A lo hi row = true)
    {A B C : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hC : 1 ≤ C) (hs : A + B + C = n)
    (m : Fin 3 → ℚ) (hid : IdQ d n a A B C m) : False := by
  obtain ⟨lo, hi, row, h1, h2, hrow⟩ := h A B hA hB (by omega)
  unfold chkRowR at hrow
  rw [List.all_eq_true] at hrow
  have hB' := hrow (B - lo) (List.mem_range.mpr (by omega))
  have e : lo + (B - lo) = B := by omega
  rw [e] at hB'
  have hcond : decide (1 ≤ B ∧ A + B < n) = true := by simp; omega
  rw [hcond] at hB'
  simp only [Bool.not_true, Bool.false_or] at hB'
  have hC' : n - A - B = C := by omega
  rw [hC'] at hB'
  exact chkCase_sound hn hredlen hred hd ha0 han (by omega) (by omega) (by omega) (by omega) hB' (by omega)
    (by omega) (by omega) (by omega) m hid

end Erdos634.Draft.GAU

#print axioms Erdos634.Draft.GAU.chkRowsR_sound
