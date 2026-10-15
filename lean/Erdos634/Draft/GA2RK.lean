/-
GA2R-K: controls for the checker.  `chkTileF fac` is `chkTile` with the constant 15 replaced by `fac`
(`chkTileF 15 = chkTile` by `rfl`).  For fac = 1 (similar-triangle solutions m = e_i, target = tile), fac = 4 (m = 2 e_i),
fac = 9 the checker REPORTS SOLUTIONS (returns false) on the ten exceptional tiles; and the real identity for fac = 1 has an explicit
solution (so `False` is not what is being proved vacuously).
-/
import Mathlib
import Erdos634.Draft.GA2RD0

namespace Erdos634.GA2R

open Erdos634.GA2R

def tgtOkF (fac : ℕ) (sl sh : ℕ → ℕ) (t1 t2 t3 A B C : ℕ) : Bool :=
  let NH := fac * sh A * sh t1 * sh t2 * sh t3
  let DL := sl B * sl C
  let NL := fac * sl A * sl t1 * sl t2 * sl t3
  let DH := sh B * sh C
  let qh := isqrt (NH / DL) + 1
  let ql := isqrt (NL / DH)
  decide (0 < DL) && decide (0 < sl t1) && decide (0 < sl t2) && decide (0 < sl t3) &&
  decide (0 < sh t3) && decide (NH ≤ qh * qh * DL) && decide (ql * ql * DH ≤ NL) &&
  noSol qh ql (sl t1) (sl t2) (sl t3) (sh t1) (sh t2) (sh t3)

def chkTileF (fac : ℕ) (sl sh : ℕ → ℕ) (n t1 t2 t3 : ℕ) : Bool :=
  (List.range n).all fun A => (List.range n).all fun B =>
    !(decide (1 ≤ A ∧ 1 ≤ B ∧ A + B < n)) || tgtOkF fac sl sh t1 t2 t3 A B (n - A - B)

theorem chkTileF_fifteen : chkTileF 15 = chkTile := rfl

/-- the ten exceptional tiles (sine-descending order), n = 30 resp. 60 -/
def ten30 : List (ℕ × ℕ × ℕ) := [(24, 5, 1), (19, 10, 1), (19, 6, 5), (18, 7, 5), (13, 12, 5), (13, 10, 7)]
def ten60 : List (ℕ × ℕ × ℕ) := [(49, 10, 1), (43, 10, 7), (37, 13, 10), (31, 19, 10)]

/-- fac = 1, 4, 9: every one of the ten tiles has a reported solution -/
theorem control_reports (fac : ℕ) (hf : fac = 1 ∨ fac = 4 ∨ fac = 9) :
    (ten30.all fun t => !(chkTileF fac (slc 2) (shc 2) 30 t.1 t.2.1 t.2.2)) = true ∧
    (ten60.all fun t => !(chkTileF fac (slc 1) (shc 1) 60 t.1 t.2.1 t.2.2)) = true := by
  rcases hf with rfl | rfl | rfl <;> decide +kernel

/-- the real fac = 1 solution behind the control: m = (1,0,0), target = tile -/
theorem control_real_witness (s1 s2 s3 : ℝ) :
    (1 * s1 + 0 * s2 + 0 * s3) ^ 2 * s2 * s3 = 1 * s1 * s1 * s2 * s3 := by ring

#print axioms control_reports

end Erdos634.GA2R
