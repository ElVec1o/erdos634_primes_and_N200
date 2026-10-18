import Mathlib.Tactic
import Erdos634.Draft.ThmDRowFar

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (R5a'): the far row across the diagonal, with `RA` at tile level proved  

`row_orient_full` = `row_orient` with its hypothesis (H2) `hfar` (and the interior-vertex hypothesis `hint`) discharged by
`hfar_of_near` (`ThmDRowFar`).  What remains as hypotheses are only facts about the *position* of the diagonal:

* the near towers `U(i, w-1-i)`, `i < w`, are present (this is `H(w)`);
* the ends `P = lp 0 w`, `Q = lp w 0` of the diagonal are frontier points of the target, `P` not a vertex of it;
* the open diagonal lies in the interior of the target; `w < v` (rigidity window of `na`).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set
  Erdos634.Draft.ThmDRowFar

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem row_orient_full (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hP : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) ∈ frontier D.target.carrier)
    (hPnv : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) ∉ Set.range D.target.pts)
    (hQ : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier) :
    ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i + 1)) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  have hfar := hfar_of_near C w hw0 hwv hnear hP hQ hint
  have hint' : ∀ i : ℕ, i + 1 < w → lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∈ interior D.target.carrier := by
    intro i hi
    have hiR : (i : ℝ) + 1 < w := by exact_mod_cast hi
    apply hint
    have hseg := lp_diag_mem_seg (u := (u : ℝ)) (v := (v : ℝ)) (ε := ε) (x := x) (s := (w : ℝ))
      (η₁ := (w : ℝ)) (η₂ := 0) (η := ηw w i) hwR.ne'
      (by rw [min_eq_right hwR.le]; unfold ηw; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
      (by rw [max_eq_left hwR.le]; unfold ηw; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)])
    have e1 : lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - ηw w i) (ηw w i) :=
      lpT_congr (by unfold ηw; ring) rfl
    have hP' : lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - w) w := lpT_congr (by ring) rfl
    have hQ' : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - 0) 0 := lpT_congr (by ring) rfl
    rw [e1]
    refine mem_openSegment_of_ne_left_right ?_ ?_ ?_
    · rw [hP']; intro h
      have := lpT_eta_eq hu huv hv2 h.symm
      unfold ηw at this; linarith
    · rw [hQ']; intro h
      have := lpT_eta_eq hu huv hv2 h.symm
      unfold ηw at this; linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    · rw [hP', hQ'] at *
      simpa [hP', hQ'] using hseg
  exact row_orient C w hnear hfar hint' (fun _ => ⟨hP, hPnv⟩)

#print axioms row_orient_full
end Erdos634.Draft.ThmDRun
