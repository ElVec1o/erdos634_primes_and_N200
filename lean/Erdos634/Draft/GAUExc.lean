/-
Draft/GAUExc.lean -- the tiles with `R ≠ R₀` at the levels `n = 30, 60` (tables for `GAUBridge.exc_of_excChk`).

`excChk n L`: every primitive ordered tile `(a0, a1, n − a0 − a1)` of level `n` either has the certificate `LemmaS.cert`
(so `R = R₀`, `LemmaS.cert_sound`) or is a rearrangement of a tile of `L`.  Checked row by row (`excRow`, one kernel
`decide` per value of `a0`: a single `decide` for `n = 60` needs 12 GB).

Pure arithmetic; no dissection.  No sorry, no native_decide.
-/
import Mathlib
import Erdos634.Draft.CaseACorF

namespace Erdos634.Draft.GAU

open Erdos634.LemmaS

/-- `t` is a rearrangement of `(x, y, z)` -/
def isPerm3 (x y z : ℕ) (t : ℕ × ℕ × ℕ) : Bool :=
  (x == t.1 && y == t.2.1 && z == t.2.2) || (x == t.1 && z == t.2.1 && y == t.2.2) ||
  (y == t.1 && x == t.2.1 && z == t.2.2) || (y == t.1 && z == t.2.1 && x == t.2.2) ||
  (z == t.1 && x == t.2.1 && y == t.2.2) || (z == t.1 && y == t.2.1 && x == t.2.2)

/-- the row `a0` of `excChk` -/
def excRow (n : ℕ) (L : List (ℕ × ℕ × ℕ)) (a0 : ℕ) : Bool :=
  (List.range n).all fun a1 =>
    if 1 ≤ a0 ∧ 1 ≤ a1 ∧ a0 + a1 < n ∧ Nat.gcd a0 (Nat.gcd a1 (n - a0 - a1)) = 1 then
      cert n a0 a1 (n - a0 - a1) || L.any (isPerm3 a0 a1 (n - a0 - a1)) else true

/-- every primitive tile of level `n` has `R = R₀` (certificate `LemmaS.cert`) or is a rearrangement of a tile in `L` -/
def excChk (n : ℕ) (L : List (ℕ × ℕ × ℕ)) : Bool := (List.range n).all (excRow n L)

theorem excChk_of_rows {n : ℕ} {L : List (ℕ × ℕ × ℕ)} (h : ∀ a0, a0 < n → excRow n L a0 = true) :
    excChk n L = true := by
  unfold excChk
  rw [List.all_eq_true]
  intro a0 ha
  exact h a0 (List.mem_range.mp ha)

/-- the tiles with `R ≠ R₀` at `n = 30` -/
def exc30 : List (ℕ × ℕ × ℕ) := [(1, 5, 24), (1, 10, 19), (5, 6, 19), (5, 7, 18), (5, 12, 13), (7, 10, 13)]

/-- the tiles with `R ≠ R₀` at `n = 60` -/
def exc60 : List (ℕ × ℕ × ℕ) := [(1, 10, 49), (7, 10, 43), (10, 13, 37), (10, 19, 31)]

theorem e30_0 : excRow 30 exc30 0 = true := by decide +kernel
theorem e30_1 : excRow 30 exc30 1 = true := by decide +kernel
theorem e30_2 : excRow 30 exc30 2 = true := by decide +kernel
theorem e30_3 : excRow 30 exc30 3 = true := by decide +kernel
theorem e30_4 : excRow 30 exc30 4 = true := by decide +kernel
theorem e30_5 : excRow 30 exc30 5 = true := by decide +kernel
theorem e30_6 : excRow 30 exc30 6 = true := by decide +kernel
theorem e30_7 : excRow 30 exc30 7 = true := by decide +kernel
theorem e30_8 : excRow 30 exc30 8 = true := by decide +kernel
theorem e30_9 : excRow 30 exc30 9 = true := by decide +kernel
theorem e30_10 : excRow 30 exc30 10 = true := by decide +kernel
theorem e30_11 : excRow 30 exc30 11 = true := by decide +kernel
theorem e30_12 : excRow 30 exc30 12 = true := by decide +kernel
theorem e30_13 : excRow 30 exc30 13 = true := by decide +kernel
theorem e30_14 : excRow 30 exc30 14 = true := by decide +kernel
theorem e30_15 : excRow 30 exc30 15 = true := by decide +kernel
theorem e30_16 : excRow 30 exc30 16 = true := by decide +kernel
theorem e30_17 : excRow 30 exc30 17 = true := by decide +kernel
theorem e30_18 : excRow 30 exc30 18 = true := by decide +kernel
theorem e30_19 : excRow 30 exc30 19 = true := by decide +kernel
theorem e30_20 : excRow 30 exc30 20 = true := by decide +kernel
theorem e30_21 : excRow 30 exc30 21 = true := by decide +kernel
theorem e30_22 : excRow 30 exc30 22 = true := by decide +kernel
theorem e30_23 : excRow 30 exc30 23 = true := by decide +kernel
theorem e30_24 : excRow 30 exc30 24 = true := by decide +kernel
theorem e30_25 : excRow 30 exc30 25 = true := by decide +kernel
theorem e30_26 : excRow 30 exc30 26 = true := by decide +kernel
theorem e30_27 : excRow 30 exc30 27 = true := by decide +kernel
theorem e30_28 : excRow 30 exc30 28 = true := by decide +kernel
theorem e30_29 : excRow 30 exc30 29 = true := by decide +kernel

theorem excChk30 : excChk 30 exc30 = true := by
  refine excChk_of_rows ?_
  intro a0 h
  interval_cases a0
  · exact e30_0
  · exact e30_1
  · exact e30_2
  · exact e30_3
  · exact e30_4
  · exact e30_5
  · exact e30_6
  · exact e30_7
  · exact e30_8
  · exact e30_9
  · exact e30_10
  · exact e30_11
  · exact e30_12
  · exact e30_13
  · exact e30_14
  · exact e30_15
  · exact e30_16
  · exact e30_17
  · exact e30_18
  · exact e30_19
  · exact e30_20
  · exact e30_21
  · exact e30_22
  · exact e30_23
  · exact e30_24
  · exact e30_25
  · exact e30_26
  · exact e30_27
  · exact e30_28
  · exact e30_29

theorem e60_0 : excRow 60 exc60 0 = true := by decide +kernel
theorem e60_1 : excRow 60 exc60 1 = true := by decide +kernel
theorem e60_2 : excRow 60 exc60 2 = true := by decide +kernel
theorem e60_3 : excRow 60 exc60 3 = true := by decide +kernel
theorem e60_4 : excRow 60 exc60 4 = true := by decide +kernel
theorem e60_5 : excRow 60 exc60 5 = true := by decide +kernel
theorem e60_6 : excRow 60 exc60 6 = true := by decide +kernel
theorem e60_7 : excRow 60 exc60 7 = true := by decide +kernel
theorem e60_8 : excRow 60 exc60 8 = true := by decide +kernel
theorem e60_9 : excRow 60 exc60 9 = true := by decide +kernel
theorem e60_10 : excRow 60 exc60 10 = true := by decide +kernel
theorem e60_11 : excRow 60 exc60 11 = true := by decide +kernel
theorem e60_12 : excRow 60 exc60 12 = true := by decide +kernel
theorem e60_13 : excRow 60 exc60 13 = true := by decide +kernel
theorem e60_14 : excRow 60 exc60 14 = true := by decide +kernel
theorem e60_15 : excRow 60 exc60 15 = true := by decide +kernel
theorem e60_16 : excRow 60 exc60 16 = true := by decide +kernel
theorem e60_17 : excRow 60 exc60 17 = true := by decide +kernel
theorem e60_18 : excRow 60 exc60 18 = true := by decide +kernel
theorem e60_19 : excRow 60 exc60 19 = true := by decide +kernel
theorem e60_20 : excRow 60 exc60 20 = true := by decide +kernel
theorem e60_21 : excRow 60 exc60 21 = true := by decide +kernel
theorem e60_22 : excRow 60 exc60 22 = true := by decide +kernel
theorem e60_23 : excRow 60 exc60 23 = true := by decide +kernel
theorem e60_24 : excRow 60 exc60 24 = true := by decide +kernel
theorem e60_25 : excRow 60 exc60 25 = true := by decide +kernel
theorem e60_26 : excRow 60 exc60 26 = true := by decide +kernel
theorem e60_27 : excRow 60 exc60 27 = true := by decide +kernel
theorem e60_28 : excRow 60 exc60 28 = true := by decide +kernel
theorem e60_29 : excRow 60 exc60 29 = true := by decide +kernel
theorem e60_30 : excRow 60 exc60 30 = true := by decide +kernel
theorem e60_31 : excRow 60 exc60 31 = true := by decide +kernel
theorem e60_32 : excRow 60 exc60 32 = true := by decide +kernel
theorem e60_33 : excRow 60 exc60 33 = true := by decide +kernel
theorem e60_34 : excRow 60 exc60 34 = true := by decide +kernel
theorem e60_35 : excRow 60 exc60 35 = true := by decide +kernel
theorem e60_36 : excRow 60 exc60 36 = true := by decide +kernel
theorem e60_37 : excRow 60 exc60 37 = true := by decide +kernel
theorem e60_38 : excRow 60 exc60 38 = true := by decide +kernel
theorem e60_39 : excRow 60 exc60 39 = true := by decide +kernel
theorem e60_40 : excRow 60 exc60 40 = true := by decide +kernel
theorem e60_41 : excRow 60 exc60 41 = true := by decide +kernel
theorem e60_42 : excRow 60 exc60 42 = true := by decide +kernel
theorem e60_43 : excRow 60 exc60 43 = true := by decide +kernel
theorem e60_44 : excRow 60 exc60 44 = true := by decide +kernel
theorem e60_45 : excRow 60 exc60 45 = true := by decide +kernel
theorem e60_46 : excRow 60 exc60 46 = true := by decide +kernel
theorem e60_47 : excRow 60 exc60 47 = true := by decide +kernel
theorem e60_48 : excRow 60 exc60 48 = true := by decide +kernel
theorem e60_49 : excRow 60 exc60 49 = true := by decide +kernel
theorem e60_50 : excRow 60 exc60 50 = true := by decide +kernel
theorem e60_51 : excRow 60 exc60 51 = true := by decide +kernel
theorem e60_52 : excRow 60 exc60 52 = true := by decide +kernel
theorem e60_53 : excRow 60 exc60 53 = true := by decide +kernel
theorem e60_54 : excRow 60 exc60 54 = true := by decide +kernel
theorem e60_55 : excRow 60 exc60 55 = true := by decide +kernel
theorem e60_56 : excRow 60 exc60 56 = true := by decide +kernel
theorem e60_57 : excRow 60 exc60 57 = true := by decide +kernel
theorem e60_58 : excRow 60 exc60 58 = true := by decide +kernel
theorem e60_59 : excRow 60 exc60 59 = true := by decide +kernel

theorem excChk60 : excChk 60 exc60 = true := by
  refine excChk_of_rows ?_
  intro a0 h
  interval_cases a0
  · exact e60_0
  · exact e60_1
  · exact e60_2
  · exact e60_3
  · exact e60_4
  · exact e60_5
  · exact e60_6
  · exact e60_7
  · exact e60_8
  · exact e60_9
  · exact e60_10
  · exact e60_11
  · exact e60_12
  · exact e60_13
  · exact e60_14
  · exact e60_15
  · exact e60_16
  · exact e60_17
  · exact e60_18
  · exact e60_19
  · exact e60_20
  · exact e60_21
  · exact e60_22
  · exact e60_23
  · exact e60_24
  · exact e60_25
  · exact e60_26
  · exact e60_27
  · exact e60_28
  · exact e60_29
  · exact e60_30
  · exact e60_31
  · exact e60_32
  · exact e60_33
  · exact e60_34
  · exact e60_35
  · exact e60_36
  · exact e60_37
  · exact e60_38
  · exact e60_39
  · exact e60_40
  · exact e60_41
  · exact e60_42
  · exact e60_43
  · exact e60_44
  · exact e60_45
  · exact e60_46
  · exact e60_47
  · exact e60_48
  · exact e60_49
  · exact e60_50
  · exact e60_51
  · exact e60_52
  · exact e60_53
  · exact e60_54
  · exact e60_55
  · exact e60_56
  · exact e60_57
  · exact e60_58
  · exact e60_59

end Erdos634.Draft.GAU

#print axioms Erdos634.Draft.GAU.excChk30
#print axioms Erdos634.Draft.GAU.excChk60
