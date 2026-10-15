import Mathlib.Tactic
import Erdos634.Draft.T30LPi3Corner

/-!
# `Pi3Enum`: the boundary enumeration as a pruned depth-first search, evaluated by the kernel

The theorems here are about the rule model (`Pi3Corner.OEdge`, `okPair`), not about a dissection.

Model.  A side with `3x` supported edges, letters `a=0,b=1,c=2`, each used `x` times (side word `(x,x,x)`), each edge oriented
(end angles `a:{β,P}`, `b:{α,P}`, `c:{α,β}`).  Rules: first start `P` and last end `P` (target corners are `P`);
adjacent ends `(en, st)` ∈ {PP, PA, PB, AB, BA} (fan rule); with `c2`: the second tile starts with `P` and the second-to-last
ends with `P`.  `sides c2 x` is the list of all such sequences, produced by a DFS with pruning (not a product).

Kernel-evaluated facts (`decide +kernel`, no `native_decide`, no new axioms):
`x=1`: 2 sides fan-only, 0 with C2; `x=2`: 108 fan-only, 4 with C2 (listed explicitly); `x=3`: 488 with C2.
Corner coupling (corner tile has an `a`-edge on one side and a `b`-edge on the other) gives 16 coupled triples at `x=2` with C2
(and 159,192 fan-only, via first/last-letter classes); the corner types `(x,y)` are computed and the L3/L4
kill rules are applied: 0 triples survive at `x = 2`.  For `x=1` there are no sides; for `x=3` sides exist and triples survive
(the rule set is not strong enough there); dropping C2 re-admits triples.
-/

namespace Erdos634.Pi3Enum

open Erdos634.Pi3Corner Ang

/-- Use one letter from the remaining counts. -/
def useL : ℕ × ℕ × ℕ → ℕ → Option (ℕ × ℕ × ℕ)
  | (ra + 1, rb, rc), 0 => some (ra, rb, rc)
  | (ra, rb + 1, rc), 1 => some (ra, rb, rc)
  | (ra, rb, rc + 1), 2 => some (ra, rb, rc)
  | _, _ => none

/-- Local rule for placing edge `e` at (0-based) position `i` of an `n`-edge side. -/
def okAt (c2 : Bool) (n i : ℕ) (prevEn : Option Ang) (e : OEdge) : Bool :=
  (match prevEn with
    | none => e.st == P
    | some p => okPair p e.st) &&
  (!(c2 && i == 1) || e.st == P) &&
  (!(c2 && i + 2 == n) || e.en == P) &&
  (i + 1 != n || e.en == P)

/-- The DFS: `k` edges still to place. -/
def ext (c2 : Bool) (n : ℕ) : ℕ → ℕ × ℕ × ℕ → Option Ang → List OEdge → List (List OEdge)
  | 0, _, _, acc => [acc.reverse]
  | k + 1, rem, pe, acc =>
    [0, 1, 2].flatMap fun l => [false, true].flatMap fun f =>
      match useL rem l with
      | none => []
      | some rem' =>
        if okAt c2 n (n - (k + 1)) pe ⟨l, f⟩ then ext c2 n k rem' (some (OEdge.en ⟨l, f⟩)) (⟨l, f⟩ :: acc)
        else []

/-- All side words with letter counts `(x,x,x)`. -/
def sides (c2 : Bool) (x : ℕ) : List (List OEdge) := ext c2 (3 * x) (3 * x) (x, x, x) none []

/-! ## Side counts -/

theorem sides_x1_fan : (sides false 1).length = 2 := by decide +kernel
/-- x = 1 control: C2 kills every side (agrees with `Pi3Corner.x1_with_C2` and the hand enumeration). -/
theorem sides_x1_c2 : (sides true 1).length = 0 := by decide +kernel
theorem sides_x2_fan : (sides false 2).length = 108 := by decide +kernel
/-- **x = 2 with C2: exactly 4 side words.** -/
theorem sides_x2_c2 : (sides true 2).length = 4 := by decide +kernel
/-- x = 3 with C2: 488 side words. -/
theorem sides_x3_c2 : (sides true 3).length = 488 := by decide +kernel

/-- The four words, as `(letter, start angle, end angle)`: the four hand configurations
`a(PB) a(PB) c(AB) c(AB) b(AP) b(AP)`, `a(PB) b(PA) c(BA) c(BA) a(BP) b(AP)`, `b(PA) a(PB) c(AB) c(AB) b(AP) a(BP)`,
`b(PA) b(PA) c(BA) c(BA) a(BP) a(BP)`. -/
def desc (w : List OEdge) : List (ℕ × Ang × Ang) := w.map fun e => (e.letter, e.st, e.en)

theorem sides_x2_c2_list :
    (sides true 2).map desc =
      [[(0, P, B), (0, P, B), (2, A, B), (2, A, B), (1, A, P), (1, A, P)],
       [(0, P, B), (1, P, A), (2, B, A), (2, B, A), (0, B, P), (1, A, P)],
       [(1, P, A), (0, P, B), (2, A, B), (2, A, B), (1, A, P), (0, B, P)],
       [(1, P, A), (1, P, A), (2, B, A), (2, B, A), (0, B, P), (0, B, P)]] := by decide +kernel

/-! ## Corner coupling, corner types, and the L3 / L4 kill rules -/

/-- Letter at position `i` of a word (junk `9` out of range). -/
def lt (w : List OEdge) (i : ℕ) : ℕ := ((w[i]?).map OEdge.letter).getD 9

/-- Letter at position `i` counted from the end (`0` = last). -/
def lr (w : List OEdge) (i : ℕ) : ℕ := lt w (w.length - 1 - i)

/-- The corner between side `p` (ending at the corner) and side `q` (starting at it): the corner tile has one `a`-edge
and one `b`-edge. -/
def coupled (p q : List OEdge) : Bool :=
  (lr p 0 == 0 && lt q 0 == 1) || (lr p 0 == 1 && lt q 0 == 0)

/-- Corner type `(x, y)`: `x` = second edge on the side carrying the corner tile's `a`-edge, `y` = on the side carrying
its `b`-edge. -/
def ctype (p q : List OEdge) : ℕ × ℕ :=
  if lr p 0 == 0 then (lr p 1, lt q 1) else (lt q 1, lr p 1)

/-- Third edge (from the corner) on the `a`-side. -/
def third (p q : List OEdge) : ℕ :=
  if lr p 0 == 0 then lr p 2 else lt q 2

/-- L3 kills type `(a,b)` when the third edge on the `a`-side is `c`; L4 kills type `(b,a)`. -/
def killed (p q : List OEdge) : Bool :=
  (ctype p q == (0, 1) && third p q == 2) || (ctype p q == (1, 0))

def triples (S : List (List OEdge)) : List (List OEdge × List OEdge × List OEdge) :=
  S.flatMap fun s1 => S.flatMap fun s2 => S.flatMap fun s3 =>
    if coupled s1 s2 && coupled s2 s3 && coupled s3 s1 then [(s1, s2, s3)] else []

def survivors (S : List (List OEdge)) : List (List OEdge × List OEdge × List OEdge) :=
  (triples S).filter fun t => !(killed t.1 t.2.1) && !(killed t.2.1 t.2.2) && !(killed t.2.2 t.1)

/-- 16 corner-coupled triples at `x = 2` with C2 (hand count: 16). -/
theorem triples_x2_c2 : (triples (sides true 2)).length = 16 := by decide +kernel

/-- **x = 2: no triple survives the L3/L4 kills** (the combinatorial core of claim T30, in the rule model). -/
theorem survivors_x2_c2 : survivors (sides true 2) = [] := by decide +kernel

/-- Each of the 16 triples is killed at some corner by L3 or L4 (same statement, spelled out). -/
theorem every_triple_killed_x2 :
    ∀ t ∈ triples (sides true 2), killed t.1 t.2.1 = true ∨ killed t.2.1 t.2.2 = true ∨ killed t.2.2 t.1 = true := by
  decide +kernel

/-! ## Controls -/

/-- Class key of a side word: first three and last three letters. -/
def key (w : List OEdge) : List ℕ := [lt w 0, lt w 1, lt w 2, lr w 0, lr w 1, lr w 2]

/-- Fan-only coupled triples at `x = 2`, counted by first/last letter classes (coupling only sees these). -/
def coupledCountFL (S : List (List OEdge)) : ℕ :=
  let cls : List (ℕ × ℕ) := [(0, 0), (0, 1), (1, 0), (1, 1)]
  let m : ℕ × ℕ → ℕ := fun fl => (S.filter fun w => lt w 0 == fl.1 && lr w 0 == fl.2).length
  (cls.map fun c1 => (cls.map fun c2 => (cls.map fun c3 =>
    if c1.2 != c2.1 && c2.2 != c3.1 && c3.2 != c1.1 then m c1 * m c2 * m c3 else 0).sum).sum).sum

/-- Hand count: 159,192 fan-only corner-coupled triples at `x = 2`. -/
theorem coupled_x2_fan : coupledCountFL (sides false 2) = 159192 := by decide +kernel

/-- Corner predicates on class keys `[f, s2, s3, l, l2, l3]` (first three letters, last three letters from the end). -/
def coupledK (p q : List ℕ) : Bool :=
  (p.getD 3 9 == 0 && q.getD 0 9 == 1) || (p.getD 3 9 == 1 && q.getD 0 9 == 0)

def killedK (p q : List ℕ) : Bool :=
  let ty : ℕ × ℕ := if p.getD 3 9 == 0 then (p.getD 4 9, q.getD 1 9) else (q.getD 1 9, p.getD 4 9)
  let th : ℕ := if p.getD 3 9 == 0 then p.getD 5 9 else q.getD 2 9
  (ty == (0, 1) && th == 2) || ty == (1, 0)

/-- Number of corner-coupled triples surviving L3/L4, counted over key classes (coupling and kills only see keys). -/
def survCountK (S : List (List OEdge)) : ℕ :=
  let cls := (S.map key).dedup
  let m : List ℕ → ℕ := fun k => (S.filter fun w => key w == k).length
  (cls.map fun c1 => (cls.map fun c2 => (cls.map fun c3 =>
    if coupledK c1 c2 && coupledK c2 c3 && coupledK c3 c1 && !killedK c1 c2 && !killedK c2 c3 && !killedK c3 c1
    then m c1 * m c2 * m c3 else 0).sum).sum).sum

/-- The key-class count agrees with the direct count at `x = 2` with C2 (0 survivors). -/
theorem survK_x2_c2 : survCountK (sides true 2) = 0 := by decide +kernel

/-- Without C2 (fan rule only), L3 and L4 leave 72,636 coupled triples at `x = 2`; C2 is what carries the proof. -/
theorem survK_x2_noC2 : survCountK (sides false 2) = 72636 := by decide +kernel

/-- The class count agrees with the direct count at `x = 2` with C2 (16). -/
theorem coupled_x2_c2_agree : coupledCountFL (sides true 2) = 16 := by decide +kernel

#print axioms sides_x2_c2
#print axioms sides_x3_c2
#print axioms survivors_x2_c2
#print axioms coupled_x2_fan

end Erdos634.Pi3Enum
