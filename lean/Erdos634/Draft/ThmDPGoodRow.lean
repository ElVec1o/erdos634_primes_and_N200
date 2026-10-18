import Mathlib.Tactic
import Erdos634.Draft.ThmDPGood
import Erdos634.Draft.ThmDRowStep
import Erdos634.Draft.ThmDRowFarRun

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.
# Theorem D' item (4): the far row with a good end `P`  

`row_orient_full_gen` : `row_orient_full` with the frontier hypotheses at `P = lp 0 w` replaced by `PGood` (fan oracle, diagonal clamp);
the end `Q = lp w 0` stays a frontier point (it lies on the side `S` of the run).
-/

open scoped Classical
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.Draft.SideRun Set
  Erdos634.Draft.ThmDRowFar Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay ε x : ℝ}

/-- points beyond a frontier end of an interior segment are outside the target -/
theorem out_beyond_frontier {K : Set Plane} (hK : Convex ℝ K) {P Q : Plane} (hPQ : P ≠ Q)
    (hint : openSegment ℝ P Q ⊆ interior K) (hQ : Q ∉ interior K) :
    ∀ y ∈ openSegment ℝ Q (AffineMap.lineMap P Q (2 : ℝ)), y ∉ K := by
  intro y hy hyK
  set d : Plane := Q - P with hd
  have hd0 : d ≠ 0 := sub_ne_zero.mpr (Ne.symm hPQ)
  have hmid : P + (1 / 2 : ℝ) • d ∈ interior K := by
    apply hint
    refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
    rw [hd]; module
  rw [openSegment_eq_image_lineMap] at hy
  obtain ⟨τ, ⟨h0, h1⟩, rfl⟩ := hy
  have hτ : 1 < 1 + τ := by linarith
  have hyτ : AffineMap.lineMap Q (AffineMap.lineMap P Q (2 : ℝ)) τ = P + (1 + τ) • d := by
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, hd]
    module
  rw [hyτ] at hyK
  have := Erdos634.Draft.ThmDRowFar.end_not_beyond' hK hd0 hmid hyK (1 + τ) hτ rfl
  have hQe : P + d = Q := by rw [hd]; abel
  rw [hQe] at this
  exact hQ this

theorem hfar_of_near_good (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hPG : PGood D (u : ℝ) (v : ℝ) ε x α (w : ℝ))
    (hQ : lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0 ∈ frontier D.target.carrier)
    (hint : openSegment ℝ (lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ)) (lpT (u : ℝ) (v : ℝ) ε x (w : ℝ) 0) ⊆
      interior D.target.carrier) :
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
  have hPQ : P ≠ Q := lpT_ne_eta hu huv hv2 hwR.ne'
  have hGP : GST (u : ℝ) (v : ℝ) ε P = -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
    rw [hPdef, GST_lp hε]; congr 1; congr 1; ring
  have hGQ : GST (u : ℝ) (v : ℝ) ε Q = -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
    rw [hQdef, GST_lp hε]; congr 1; congr 1; ring
  obtain ⟨P', hGP', hP'm, hclP⟩ := hPG.diagclamp
  set Q' : Plane := AffineMap.lineMap P Q (2 : ℝ) with hQ'
  have hGQ' : GST (u : ℝ) (v : ℝ) ε Q' = -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
    rw [hQ', lineMap_lin, hGP, hGQ]; ring
  have hQ'm : Q ∈ openSegment ℝ P Q' := by
    rw [openSegment_eq_image_lineMap]
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    rw [hQ']
    simp only [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add]
    module
  have hout := out_beyond_frontier D.target.convex hPQ hint hQ.2
  exact hfar_of_near_run C w hw0 hwv hnear hint (P' := P') (Q' := Q') (by rw [hGP', hGP]) hGQ' hP'm hQ'm
    (fun e _ => hclP e.1 e.2)
    (fun e _ => not_straddles_of_outside D.toDissection
      (fun y hy => hout y (by rw [openSegment_symm]; exact hy)) e.1 e.2)

/-- **The row step with a good end.** -/
theorem row_orient_full_gen (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ) (hw0 : 0 < w) (hwv : w < v)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hPG : PGood D (u : ℝ) (v : ℝ) ε x α (w : ℝ))
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
  have hfar := hfar_of_near_good C w hw0 hwv hnear hPG hQ hint
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
  have hP1 : lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) = lpT (u : ℝ) (v : ℝ) ε x 0 (w : ℝ) :=
    lpT_congr (by simp) (by unfold ηw; simp)
  refine row_orient_gen C w hnear hfar hint' (fun hw tW tE hne hvW hvE a a' hW hE => ?_)
  rw [hP1] at hvW hvE hW hE
  exact hPG.fan tW tE hne hvW hvE a a' hW hE

#print axioms hfar_of_near_good
#print axioms row_orient_full_gen
end Erdos634.Draft.ThmDRun
