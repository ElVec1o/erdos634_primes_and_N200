import Mathlib.Tactic
import Erdos634.Draft.ThmDStep33

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: 'how not to start a run' (their Lemma 33, p. 28).
# Theorem D' (R5): Lemma 33 step `H(w) => H(w+1)` from Lemma 32 (the trapezoid lemma)  

`step33` : with `H(w)`, the run tile `Δ_{w,0}`, the ends `P`, `Q` of the diagonal on the sides, and **Lemma 32 as a hypothesis**
(`L32Hyp`: `T(s,r)` and a `b`-edge running east on `ℓ_r` from `x(i0,r)`, `i0 + r < s ≤ n`, cannot coexist), the triangle
`H(w+1)` occurs.  Pieces: the far row of `∇`'s (`row_orient_full`, the H2 theorem), the `α`-tiles `G_j` at the interior diagonal
vertices (`sector_dichotomy_UD`) and at `P` (`sector_dichotomy_PD`), the least `j*` with `G_{j*}` not `Δ`, `T(w+1, j*)`, and Lemma 32.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg Erdos634.Draft.ThmDRowFar

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- **Lemma 32 (trapezoid lemma), as the hypothesis of the induction**: for `1 ≤ r < s ≤ n`, `i0 + r < s`, `T(s,r)` and a tile
north of `ℓ_r` with `α` at `x(i0,r)` and a `b`-edge east cannot coexist. -/
def L32Hyp (D : CongruentDissection N) (u v ε x α : ℝ) (n : ℕ) : Prop :=
  ∀ s r i0 : ℕ, 1 ≤ r → r < s → s ≤ n → i0 + r < s → TrapT D u v ε x s r →
    BEastT D u v ε x α (i0 : ℝ) (r : ℝ) → False

theorem UTT_congr {u v ε x a b a' b' : ℝ} (h : UTT D u v ε x a b) (ha : a = a') (hb : b = b') : UTT D u v ε x a' b' := by
  subst ha hb; exact h

theorem DTT_congr {u v ε x a b a' b' : ℝ} (h : DTT D u v ε x a b) (ha : a = a') (hb : b = b') : DTT D u v ε x a' b' := by
  subst ha hb; exact h

theorem BEastT_congr {u v ε x α a b a' b' : ℝ} (h : BEastT D u v ε x α a b) (ha : a = a') (hb : b = b') :
    BEastT D u v ε x α a' b' := by
  subst ha hb; exact h

/-- interior diagonal vertices are interior to the target -/
theorem diag_vertex_interior (S : SetupT D u v α β γ L ax ay) (hε : ε ^ 2 = 1) {w : ℕ} (hw : 0 < w) {η : ℝ}
    (hη0 : 0 < η) (hηw : η < w)
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier) :
    lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η ∈ interior D.target.carrier := by
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  apply hint
  have hseg := lp_diag_mem_seg (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := (w : ℝ))
    (η₁ := (w : ℝ)) (η₂ := 0) (η := η) hwR.ne'
    (by rw [min_eq_right hwR.le]; exact hη0.le) (by rw [max_eq_left hwR.le]; exact hηw.le)
  have hP' : lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - w) w := lpT_congr (by ring) rfl
  have hQ' : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - 0) 0 := lpT_congr (by ring) rfl
  rw [hP', hQ']
  refine mem_openSegment_of_ne_left_right ?_ ?_ hseg
  · intro h
    have := lpT_eta_eq hu huv hv2 h.symm
    linarith
  · intro h
    have := lpT_eta_eq hu huv hv2 h.symm
    linarith

#print axioms diag_vertex_interior
end Erdos634.Draft.ThmDRun
