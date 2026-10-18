import Mathlib.Tactic
import Erdos634.Draft.ThmDPGood
import Erdos634.Draft.ThmDSector4

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): the row part of `PGood`  

`PRow D u v ε x η` : `P = lp 0 η` lies in the target and the row through it is clamped west of `P`; this is all that the trapezoid lemma
(Lemma 32, step A) uses at `P`.  `PGood.toRow`; `PRow_of_frontier` for a frontier point of a side line (corner start).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.RunPartition Erdos634.Draft.SideRun Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

structure PRow (D : CongruentDissection N) (u v ε x η : ℝ) : Prop where
  mem : lpT u v ε x 0 η ∈ D.target.carrier
  rowclamp : ∃ s0 : ℝ, 0 < s0 ∧ ∀ (Q : Plane) (i : Fin N) (k : Fin 3),
    ¬ Straddles ((D.tile i).edge k) (lpT u v ε x (-s0) η) (lpT u v ε x 0 η) Q

theorem PGood.toRow {u v ε x α η : ℝ} (h : PGood D u v ε x α η) : PRow D u v ε x η :=
  ⟨h.mem, h.rowclamp⟩

theorem PRow_of_frontier (C : CtxBaseT D u v α β γ L ax ay ε x) {η : ℝ}
    (hPf : lpT (u : ℝ) (v : ℝ) ε x 0 η ∈ frontier D.target.carrier)
    (hside : (ε = 1 ∧ gA ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0) ∨
      (ε = -1 ∧ gB L ax ay (lpT (u : ℝ) (v : ℝ) ε x 0 η) = 0)) :
    PRow D (u : ℝ) (v : ℝ) ε x η := by
  refine ⟨D.target.isCompact.isClosed.frontier_subset hPf, 1, one_pos, fun Q i k => ?_⟩
  have hout : ∀ y ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x (-1) η) (lpT (u : ℝ) (v : ℝ) ε x 0 η),
      y ∉ D.target.carrier := by
    intro y hy
    rw [openSegment_eq_image_lineMap] at hy
    obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
    rw [lineMap_lpT]
    have := west_outside C.S C.hε hside (δ := 1 - τ) (by linarith)
    rwa [show lpT (u : ℝ) (v : ℝ) ε x (-1 + τ * (0 - -1)) (η + τ * (η - η))
      = lpT (u : ℝ) (v : ℝ) ε x (0 - (1 - τ)) η from lpT_congr (by ring) (by ring)]
  exact not_straddles_of_outside D.toDissection hout i k

#print axioms PRow_of_frontier
end Erdos634.Draft.ThmDRun
