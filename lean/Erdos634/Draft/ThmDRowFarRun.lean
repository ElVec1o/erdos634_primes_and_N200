import Mathlib.Tactic
import Erdos634.Draft.ThmDRowFar
import Erdos634.RunPartition

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (H2, blocked form): the far row of a partial diagonal, ends clamped by non-straddling  

`hfar_of_near_run` : `hfar_of_near` for a diagonal `PQ` whose ends are not frontier points of the target but are *clamped*
(`RunPartition.run_partition`: no far-side chain edge straddles `P` or `Q`).  The far chain edges contained in `PQ` then partition it
(`run_partition`), the rigidity window forces them all to be `a`-edges, and the counting form of the interval lemma
(`interval_tiling_card`: `w` unit intervals with disjoint interiors in `[0,w]` start at every integer) places them.
Used for the diagonal `σ = q_0 R` of the trapezoid lemma, whose upper end `R` is interior to the target.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set
  Erdos634.Draft.ThmDRowFar Erdos634.Draft.ThmDRowIntervals

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem hfar_of_near_run (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier)
    {P' Q' : Plane}
    (hfP' : GST (u : ℝ) (v : ℝ) ε P' = -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ))
    (hfQ' : GST (u : ℝ) (v : ℝ) ε Q' = -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ))
    (hP'm : lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) ∈ openSegment ℝ P' (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0))
    (hQ'm : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) Q')
    (hclP : ∀ e ∈ D.toDissection.lineChain (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x (w : ℝ)),
      ¬ Straddles ((D.tile e.1).edge e.2) P' (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0))
    (hclQ : ∀ e ∈ D.toDissection.lineChain (GST (u : ℝ) (v : ℝ) ε) (-lvT (u : ℝ) (v : ℝ) ε x (w : ℝ)),
      ¬ Straddles ((D.tile e.1).edge e.2) Q' (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ))) :
    ∀ i : ℕ, i < w → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
  have S := C.S
  have hε := C.e2
  have hu := S.u0
  have huv := S.uv'
  have hv2 := S.v2
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw0
  set P := lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) with hPdef
  set Q := lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 with hQdef
  set g := GST (u : ℝ) (v : ℝ) ε with hgdef
  set c : ℝ := -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) with hcdef
  have hg : g ≠ 0 := GST_ne hu huv hv2 hε
  have hPQ : P ≠ Q := by
    rw [hPdef, hQdef]; exact lpT_ne_eta hu huv hv2 hwR.ne'
  have hdiag : ∀ η : ℝ, g (lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - η) η) = c := by
    intro η
    rw [hgdef, GST_lp hε, show (w : ℝ) - η + η = w by ring]
  have hP' : P = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - w) w := lpT_congr (by ring) rfl
  have hQ' : Q = lpT (u : ℝ) (v : ℝ) ε x ((w : ℝ) - 0) 0 := lpT_congr (by ring) rfl
  have hS : segment ℝ P Q ⊆ {y | g y = c} := by
    intro y hy
    rw [hP', hQ'] at hy
    obtain ⟨η, -, -, rfl⟩ := diag_seg_param hy
    exact hdiag η
  have hwall : ∀ y ∈ openSegment ℝ P Q, ∀ j, y ∉ interior (D.tile j).carrier := near_wall C w hw0 hnear
  have hsumF := run_partition D.toDissection g hg c hPQ hfP' hfQ' hP'm hQ'm hS hint hwall hclP hclQ
  refine hfar_of_near_data C w hw0 hwv hnear
    ((D.toDissection.lineChain g c).filter (fun e => (D.tile e.1).edge e.2 ⊆ segment ℝ P Q))
    (fun e he => (Finset.mem_filter.mp he).1) (fun e he => (Finset.mem_filter.mp he).2) hsumF ?_
  intro e₁ h₁ e₂ h₂ hne
  have h₁' := (Finset.mem_filter.mp h₁).1
  have h₂' := (Finset.mem_filter.mp h₂).1
  obtain ⟨-, -, hle₁⟩ := Dissection.mem_lineChain.mp h₁'
  obtain ⟨-, -, hle₂⟩ := Dissection.mem_lineChain.mp h₂'
  exact D.toDissection.sameside_edges_subsingleton g c hg hne
    ((D.tile e₁.1).carrier_subset_halfplane g c hle₁)
    ((D.tile e₂.1).carrier_subset_halfplane g c hle₂)
    (D.toDissection.lineChain_edge_subset h₁') (D.toDissection.lineChain_edge_subset h₂')

#print axioms hfar_of_near_run
end Erdos634.Draft.ThmDRun
