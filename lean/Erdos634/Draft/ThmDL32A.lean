import Mathlib.Tactic
import Erdos634.Draft.ThmDStep33c
import Erdos634.Draft.ThmDL32Lines
import Erdos634.Draft.ThmDL32Cover

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the trapezoid lemma for a stopped run (their Lemma 32, p. 26).
# Theorem D' (Lemma 32, step A): `R = x(s-r,r)` lies in the interior of an edge of a tile north of `ℓ_r`  

Beeson-Rosu Lemma 32, first paragraph: with `T(s,r)` and a `b`-edge running east on `ℓ_r` from `x(i0,r)`, `R` is not an endpoint of a
north-side chain edge on `ℓ_r` (else the chain edges between `x(0,r)` and `R` would decompose `(s-r) c` with a `b`-edge, against the
rigidity window `RC`: `chord_c`, `s-r < v`), hence lies in the relative interior of one.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem straddles_symm {E : Set Plane} {P' P Q : Plane} : Straddles E P' P Q ↔ Straddles E Q P P' := by
  unfold Straddles
  rw [openSegment_symm ℝ P' P, openSegment_symm ℝ P Q]
  exact And.comm

/-- the `i`-th `∇` of the row below `ℓ_r` as `HasV` with real coordinates -/
theorem trap_nabla {s r : ℕ} (Tt : TrapT D (u : ℝ) (v : ℝ) ε x s r) (hr : 1 ≤ r) {i : ℕ} (hi : i + r + 1 ≤ s) :
    ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) ((r : ℝ) - 1)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (r : ℝ))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (r : ℝ)) := by
  obtain ⟨t, ht⟩ := Tt.2 i (r - 1) (by omega) (by omega)
  have hc : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := Nat.cast_pred (by omega)
  refine ⟨t, hasV_congr ht (lpT_congr rfl hc) (lpT_congr rfl (by rw [hc]; ring)) (lpT_congr rfl (by rw [hc]; ring))⟩

end Erdos634.Draft.ThmDRun
