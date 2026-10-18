import Erdos634.Draft.ThmCRigidity

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' run port, module 5: real partition equations to the rigidity windows  (DRAFT, NOT COMPILED, )

Written 2026-10-18 while the Lean slot was busy; never run through `lake`/`lean`.  Not in `All`.  Imports only
`ThmCRigidity` (compiled? NO: `ThmC*` are themselves uncompiled drafts).

Port target: `SideRunGArith` (`A1`, `A5`, `Aa`, `C_QB`, `C_base`, `C_AQ`: the arithmetic of the chord principle) and
`SideRunGChordB` (`exists_bR`, `rep_nat_b`, `rep_nat_a`, `first_len_jbG`), `SideRunGRow.rep_nat_c`.

For the base-beta tile the rigidity windows of the three decompositions are all `f`.  For the gamma = 2 alpha tile they are
**(RA) `n a`: `v`, (RB) `n b`: `u`, (RC) `n c`: no `b` below `v`, pure below `u`** (`ThmCRigidity.rigid_a/b/c`; sharp).
This module restates them in the form the lattice induction consumes:

* `exists_bT`, `rep_nat_a/b/c` : a REAL partition equation `x a + y b + z c = j · (side)` with natural multiplicities is the
  NATURAL equation (the sides are `u², v² − u², u v`);
* `chord_a`, `chord_b`, `chord_c` : the windowed conclusions;
* `first_len_ja` (`j < v`), `first_len_jb` (`j < u`), `first_len_jc` (`j < u`): **the first edge of a clamped chord of length
  `j·side` is that side** (Lemma A1 / Aa analogues); `no_b_jc` (`j < v`): a chord of length `j c`, `j < v`, has no `b`.

DIFFERENCE FROM BASE-BETA (matters for the ordering of the port): the `b`-chord window is `u`, smaller than `v`.  In
`SideRunGChordB.chordG` the chord from a lattice point along the `v⃗`-direction has length `j b`; with window `u` the lattice
induction for the gamma = 2 alpha tile can use `chordG` only up to `j < u`.  Lemma K needs rows up to `v − 1`; in the hand
proof the `b`-rigidity is not used there (the wall `S′` supplies the `b`-edges: `K4`) -- see `thmD_port_plan.md` §R-chord.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Draft.ThmC

variable {u v : ℕ}

theorem exists_bT (huv : u < v) : ∃ b : ℕ, b + u * u = v * v ∧ (b : ℝ) = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
  have h : u * u ≤ v * v := Nat.mul_le_mul huv.le huv.le
  refine ⟨v * v - u * u, Nat.sub_add_cancel h, ?_⟩
  rw [Nat.cast_sub h]
  push_cast
  ring

/-- real `x a + y b + z c = j a` is the natural equation -/
theorem rep_nat_a (huv : u < v) {x y z j : ℕ}
    (h : (x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v) = (j : ℝ) * (u : ℝ) ^ 2) :
    ∃ b : ℕ, b + u * u = v * v ∧ x * (u * u) + y * b + z * (u * v) = j * (u * u) := by
  obtain ⟨b, hbN, hbR⟩ := exists_bT huv
  refine ⟨b, hbN, ?_⟩
  rw [← hbR] at h
  have h' : ((x * (u * u) + y * b + z * (u * v) : ℕ) : ℝ) = ((j * (u * u) : ℕ) : ℝ) := by
    push_cast; linarith [h]
  exact_mod_cast h'

/-- real `x a + y b + z c = j b` is the natural equation -/
theorem rep_nat_b (huv : u < v) {x y z j : ℕ}
    (h : (x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v) =
      (j : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2)) :
    ∃ b : ℕ, b + u * u = v * v ∧ x * (u * u) + y * b + z * (u * v) = j * b := by
  obtain ⟨b, hbN, hbR⟩ := exists_bT huv
  refine ⟨b, hbN, ?_⟩
  rw [← hbR] at h
  have h' : ((x * (u * u) + y * b + z * (u * v) : ℕ) : ℝ) = ((j * b : ℕ) : ℝ) := by
    push_cast; linarith [h]
  exact_mod_cast h'

/-- real `x a + y b + z c = j c` is the natural equation -/
theorem rep_nat_c (huv : u < v) {x y z j : ℕ}
    (h : (x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v) = (j : ℝ) * ((u : ℝ) * v)) :
    ∃ b : ℕ, b + u * u = v * v ∧ x * (u * u) + y * b + z * (u * v) = j * (u * v) := by
  obtain ⟨b, hbN, hbR⟩ := exists_bT huv
  refine ⟨b, hbN, ?_⟩
  rw [← hbR] at h
  have h' : ((x * (u * u) + y * b + z * (u * v) : ℕ) : ℝ) = ((j * (u * v) : ℕ) : ℝ) := by
    push_cast; linarith [h]
  exact_mod_cast h'

/-! ### The windows -/

theorem chord_a (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) {x y z j : ℕ} (hj : j < v)
    (h : (x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v) = (j : ℝ) * (u : ℝ) ^ 2) :
    x = j ∧ y = 0 ∧ z = 0 := by
  obtain ⟨b, hbN, hn⟩ := rep_nat_a huv h
  exact rigid_a hcop hu huv hbN hj hn.symm

theorem chord_b (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) {x y z j : ℕ} (hj : j < u)
    (h : (x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v) =
      (j : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2)) :
    x = 0 ∧ y = j ∧ z = 0 := by
  obtain ⟨b, hbN, hn⟩ := rep_nat_b huv h
  exact rigid_b hcop hu huv hbN hj hn.symm

/-- a chord of length `j c`: no `b` below `v`, and the pure decomposition below `u` -/
theorem chord_c (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) {x y z j : ℕ}
    (h : (x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v) = (j : ℝ) * ((u : ℝ) * v)) :
    (j < v → y = 0) ∧ (j < u → x = 0 ∧ y = 0 ∧ z = j) := by
  obtain ⟨b, hbN, hn⟩ := rep_nat_c huv h
  exact rigid_c hcop hu huv hbN hn.symm

/-! ### First edge of a clamped chord (Lemma A1 / Aa analogues) -/

/-- **The first edge of a chord of length `j b`, `j < u`, is a `b`-edge.**  -/
theorem first_len_jb (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) {x y z j : ℕ} (hj : j < u)
    {ℓ : ℝ} (hℓ : ℓ = (u : ℝ) ^ 2 ∨ ℓ = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∨ ℓ = (u : ℝ) * v)
    (h : ℓ + ((x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v)) =
      (j : ℝ) * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2)) :
    ℓ = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 := by
  rcases hℓ with rfl | rfl | rfl
  · exfalso
    have := chord_b hcop hu huv (x := x + 1) (y := y) (z := z) (j := j) hj (by push_cast; linarith)
    omega
  · rfl
  · exfalso
    have := chord_b hcop hu huv (x := x) (y := y) (z := z + 1) (j := j) hj (by push_cast; linarith)
    omega

/-- **The first edge of a chord of length `j a`, `j < v`, is an `a`-edge.** -/
theorem first_len_ja (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) {x y z j : ℕ} (hj : j < v)
    {ℓ : ℝ} (hℓ : ℓ = (u : ℝ) ^ 2 ∨ ℓ = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∨ ℓ = (u : ℝ) * v)
    (h : ℓ + ((x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v)) =
      (j : ℝ) * (u : ℝ) ^ 2) :
    ℓ = (u : ℝ) ^ 2 := by
  rcases hℓ with rfl | rfl | rfl
  · rfl
  · exfalso
    have := chord_a hcop hu huv (x := x) (y := y + 1) (z := z) (j := j) hj (by push_cast; linarith)
    omega
  · exfalso
    have := chord_a hcop hu huv (x := x) (y := y) (z := z + 1) (j := j) hj (by push_cast; linarith)
    omega

/-- **The first edge of a chord of length `j c`, `j < u`, is a `c`-edge.** -/
theorem first_len_jc (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) {x y z j : ℕ} (hj : j < u)
    {ℓ : ℝ} (hℓ : ℓ = (u : ℝ) ^ 2 ∨ ℓ = (v : ℝ) ^ 2 - (u : ℝ) ^ 2 ∨ ℓ = (u : ℝ) * v)
    (h : ℓ + ((x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v)) =
      (j : ℝ) * ((u : ℝ) * v)) :
    ℓ = (u : ℝ) * v := by
  rcases hℓ with rfl | rfl | rfl
  · exfalso
    have := (chord_c hcop hu huv (x := x + 1) (y := y) (z := z) (j := j) (by push_cast; linarith)).2 hj
    omega
  · exfalso
    have := (chord_c hcop hu huv (x := x) (y := y + 1) (z := z) (j := j) (by push_cast; linarith)).2 hj
    omega
  · rfl

/-- a chord of length `j c`, `j < v`, contains no `b`-edge (so the first edge is `a` or `c`) -/
theorem no_b_jc (hcop : Nat.Coprime u v) (hu : 0 < u) (huv : u < v) {x y z j : ℕ} (hj : j < v)
    (h : (x : ℝ) * (u : ℝ) ^ 2 + y * ((v : ℝ) ^ 2 - (u : ℝ) ^ 2) + z * ((u : ℝ) * v) = (j : ℝ) * ((u : ℝ) * v)) :
    y = 0 :=
  (chord_c hcop hu huv h).1 hj

/-! ### Witness: the windows are attained (sharpness, so the hypotheses are not vacuous) -/

/-- `v a = u c` : the window of RA is exactly `v` -/
theorem window_a_sharp (u v : ℕ) : v * (u * u) = 0 * (u * u) + 0 * (v * v - u * u) + u * (u * v) :=
  ra_sharp u v

end Erdos634.Draft.ThmDRun

#print axioms Erdos634.Draft.ThmDRun.exists_bT
#print axioms Erdos634.Draft.ThmDRun.rep_nat_a
#print axioms Erdos634.Draft.ThmDRun.rep_nat_b
#print axioms Erdos634.Draft.ThmDRun.rep_nat_c
#print axioms Erdos634.Draft.ThmDRun.chord_a
#print axioms Erdos634.Draft.ThmDRun.chord_b
#print axioms Erdos634.Draft.ThmDRun.chord_c
#print axioms Erdos634.Draft.ThmDRun.first_len_jb
#print axioms Erdos634.Draft.ThmDRun.first_len_ja
#print axioms Erdos634.Draft.ThmDRun.first_len_jc
#print axioms Erdos634.Draft.ThmDRun.no_b_jc
#print axioms Erdos634.Draft.ThmDRun.window_a_sharp
