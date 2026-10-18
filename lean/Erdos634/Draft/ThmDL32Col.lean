import Mathlib.Tactic
import Erdos634.Draft.ThmDL32A2
import Erdos634.Draft.ThmDRowFarRun
import Erdos634.Draft.ThmDRowOrient2

/-!
# Theorem D' (Lemma 32, step B): the east chain of the diagonal `σ = q_0 R` is the column of `∇`'s  

* `lpT_shift`, `lvT_shift` : translating the origin by `a` steps along the base shifts `ξ` by `a`, and the level by `a`;
* `col_orient'` : the far (east) tiles across the `a`-edges of a clamped partial diagonal `[R, q_0]` are `∇`'s, given that the
  top far tile has `β` at its upper end (hypothesis `hbase`): `hfar_of_near_run` + `row_orient_base`.
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set Erdos634.Draft.APrimeSeat1
  Erdos634.Draft.APrimeLeg

theorem lpT_shift (u v ε x a ξ η : ℝ) :
    lpT u v ε x ξ η = lpT u v ε (x + ε * a * (u * v)) (ξ - a) η := by
  unfold lpT
  exact mkPt_congr (by ring) rfl

theorem lvT_shift {u v ε x : ℝ} (hε : ε ^ 2 = 1) (a r : ℝ) :
    lvT u v ε (x + ε * a * (u * v)) r = lvT u v ε x (a + r) := by
  unfold lvT
  linear_combination (hhT u v * a * (u * v)) * hε

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem col_orient' (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
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
      ¬ Straddles ((D.tile e.1).edge e.2) Q' (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)))
    (hbase : 0 < w → ∀ (t : Fin N) (k m : Fin 3), k ≠ m →
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x (((0 : ℕ) : ℝ) + 1) (ηw w 0) →
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) →
      (∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ)) →
      (D.tile t).localAngle (lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1)) = β) :
    ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i + 1)) := by
  have S := C.S
  have hε := C.e2
  have hfar := hfar_of_near_run C w hw0 hwv hnear hint hfP' hfQ' hP'm hQ'm hclP hclQ
  have hint' : ∀ i : ℕ, i + 1 < w → lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∈ interior D.target.carrier := by
    intro i hi
    have hiR : (i : ℝ) + 1 < w := by exact_mod_cast hi
    have hηpos : 0 < ηw w i := by unfold ηw; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    have hηlt : ηw w i < w := by unfold ηw; have : (0 : ℝ) ≤ i := Nat.cast_nonneg i; linarith
    have := diag_vertex_interior S hε hw0 hηpos hηlt hint
    rwa [show (w : ℝ) - ηw w i = (i : ℝ) + 1 by unfold ηw; ring] at this
  exact row_orient_base C w hnear hfar hint' hbase

#print axioms col_orient'
end Erdos634.Draft.ThmDRun
