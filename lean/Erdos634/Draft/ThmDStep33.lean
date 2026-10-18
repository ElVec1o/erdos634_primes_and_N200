import Mathlib.Tactic
import Erdos634.Draft.ThmDSector4

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: 'how not to start a run' (their Lemma 33, p. 28).
# Theorem D' (R5): the lattice-tile forms of the sector step; `TrapT`, `HT`  

`sector_dichotomy_UD` / `sector_dichotomy_PD` : `sector_dichotomy` / `sector_dichotomy_P` with the five (two) tiles given as
`UTT`/`DTT` facts (`Δ_{i,j}`, `∇_{i,j}` are tiles).  `TrapT s r` is the paper's `T(s,r)` (rows `j < r`, `Δ_{i,j}` for `i+j ≤ s-1`,
`∇_{i,j}` for `i+j ≤ s-2`), `HT w = TrapT w w`.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **`T(s,r)` occurs**: the trapezoid of Beeson-Rosu Def. 11.1 (`Δ_{i,j}`: `j < r`, `i + j ≤ s - 1`; `∇_{i,j}`: `j < r`, `i + j ≤ s - 2`). -/
def TrapT (D : CongruentDissection N) (u v ε x : ℝ) (s r : ℕ) : Prop :=
  (∀ i j : ℕ, j < r → i + j + 1 ≤ s → UTT D u v ε x (i : ℝ) (j : ℝ)) ∧
  (∀ i j : ℕ, j < r → i + j + 2 ≤ s → DTT D u v ε x (i : ℝ) (j : ℝ))

/-- `H(w)`: the triangle `U x(w,0) x(0,w)` is quadratically tiled -/
def HT (D : CongruentDissection N) (u v ε x : ℝ) (w : ℕ) : Prop := TrapT D u v ε x w w

theorem sector_dichotomy_UD (C : CtxBaseT D u v α β γ L ax ay ε x) {ξ η : ℝ}
    (hx : lpT (u : ℝ) (v : ℝ) ε x ξ η ∈ interior D.target.carrier)
    (u1 : UTT D (u : ℝ) (v : ℝ) ε x (ξ - 1) η) (u2 : UTT D (u : ℝ) (v : ℝ) ε x ξ (η - 1))
    (d3 : DTT D (u : ℝ) (v : ℝ) ε x (ξ - 1) (η - 1)) (d4 : DTT D (u : ℝ) (v : ℝ) ε x (ξ - 1) η)
    (d5 : DTT D (u : ℝ) (v : ℝ) ε x ξ (η - 1)) :
    UTT D (u : ℝ) (v : ℝ) ε x ξ η ∨ BEastT D (u : ℝ) (v : ℝ) ε x α ξ η := by
  obtain ⟨t1, h1⟩ := u1
  obtain ⟨t2, h2⟩ := u2
  obtain ⟨t3, h3⟩ := d3
  obtain ⟨t4, h4⟩ := d4
  obtain ⟨t5, h5⟩ := d5
  refine sector_dichotomy C hx (t1 := t1) (t2 := t2) (t3 := t3) (t4 := t4) (t5 := t5) ?_ ?_ ?_ ?_ ?_
  · exact hasV_congr h1 rfl (lpT_congr (by ring) rfl) rfl
  · exact hasV_congr h2 rfl rfl (lpT_congr rfl (by ring))
  · exact hasV_congr h3 (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring)) (lpT_congr (by ring) (by ring))
  · exact hasV_congr h4 (lpT_congr (by ring) rfl) rfl (lpT_congr (by ring) rfl)
  · exact hasV_congr h5 rfl (lpT_congr rfl (by ring)) (lpT_congr rfl (by ring))

theorem sector_dichotomy_PD (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ} (hη : 0 < η)
    (hPf : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ frontier D.target.carrier)
    (hPnv : lpT (u : ℝ) (v : ℝ) ε x 0 η ∉ Set.range D.target.pts)
    (hside : (ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0) ∨
      (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0))
    (uD : UTT D (u : ℝ) (v : ℝ) ε x 0 (η - 1)) (dN : DTT D (u : ℝ) (v : ℝ) ε x 0 (η - 1)) :
    UTT D (u : ℝ) (v : ℝ) ε x 0 η ∨ BEastT D (u : ℝ) (v : ℝ) ε x α 0 η := by
  obtain ⟨tD, hD⟩ := uD
  obtain ⟨tN, hN⟩ := dN
  refine sector_dichotomy_P C hη hPf hPnv hside (tD := tD) (tN := tN) ?_ ?_
  · exact hasV_congr hD rfl (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring))
  · exact hasV_congr hN (lpT_congr (by ring) rfl) (lpT_congr rfl (by ring)) (lpT_congr (by ring) (by ring))

#print axioms sector_dichotomy_UD
#print axioms sector_dichotomy_PD
end Erdos634.Draft.ThmDRun
