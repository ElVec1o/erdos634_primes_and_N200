import Mathlib.Tactic
import Erdos634.Draft.ThmDWall
import Erdos634.Draft.ThmDRunLattice
import Erdos634.Draft.APrimeLeg

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): what the run lemmas need at the ray end `P = lp 0 η`  

`PGood D u v ε x α η` bundles the four facts about the end `P = lp 0 η` of the ray `UP` that Lemmas 32/33 use:
the point lies in the target; the fan oracle at `P` for two tiles with a vertex there; the angle sum `π` over a finite set `U`
containing every tile with a vertex at `P`; the clamp of the row through `P` and of the diagonal through `P` on the west side.
At a frontier non-vertex of a side of the target (corner start) they follow from `pinfan_ang`, `pin_angle_sum`, `west_outside`;
at a wall point (interior start, tile `T₀` across the ray) from `WestCover` (`pinfan_wall`, `wall_east_sum`, `WestCover.no_straddle`).
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.RunPartition Set Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ}

structure PGood (D : CongruentDissection N) (u v ε x α η : ℝ) : Prop where
  mem : lpT u v ε x 0 η ∈ D.target.carrier
  fan : ∀ (tW tE : Fin N), tW ≠ tE → (∃ k, (D.tile tW).pts k = lpT u v ε x 0 η) →
    (∃ k, (D.tile tE).pts k = lpT u v ε x 0 η) → ∀ a a' : Ang,
    (D.tile tW).localAngle (lpT u v ε x 0 η) = angVal α a →
    (D.tile tE).localAngle (lpT u v ε x 0 η) = angVal α a' →
    ∃ m : Cnt, Fan (Cnt.add (Cnt.add a.cnt a'.cnt) m)
  usum : ∃ U : Finset (Fin N), ∑ i ∈ U, (D.tile i).localAngle (lpT u v ε x 0 η) = Real.pi ∧
    ∀ τ k, (D.tile τ).pts k = lpT u v ε x 0 η → τ ∈ U
  rowclamp : ∃ s0 : ℝ, 0 < s0 ∧ ∀ (Q : Plane) (i : Fin N) (k : Fin 3),
    ¬ Straddles ((D.tile i).edge k) (lpT u v ε x (-s0) η) (lpT u v ε x 0 η) Q
  diagclamp : ∃ P' : Plane, GST u v ε P' = GST u v ε (lpT u v ε x 0 η) ∧
    lpT u v ε x 0 η ∈ openSegment ℝ P' (lpT u v ε x η 0) ∧
    ∀ (i : Fin N) (k : Fin 3),
      ¬ Straddles ((D.tile i).edge k) P' (lpT u v ε x 0 η) (lpT u v ε x η 0)

end Erdos634.Draft.ThmDRun
