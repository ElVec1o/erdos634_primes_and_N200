import Mathlib.Tactic
import Erdos634.Draft.ThmDRowOrient

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours. Here: the row induction on a run (their Lemmas 32-34, Theorem 37).
# Theorem D' (R5): `row_orient` with the base case given as a hypothesis  

`row_orient_base` is `row_orient` with the fan at the frontier end `P` replaced by the hypothesis that the top far tile has
`β` at its upper end (which `Lemma 32` obtains from the angle sum at the interior point `R`).
-/

open scoped Classical
open Metric
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.RunPartition Erdos634.TilePlacement Erdos634.Draft.SideRun Set
  Erdos634.Draft.ThmDHalf Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

variable {N : ℕ} {D : CongruentDissection N}

/-- `row_orient_comb` with the base case given directly -/
theorem row_orient_comb' (w : ℕ) (T : ℕ → Bool)
    (hmid : ∀ i, i + 1 < w → ∃ m : Cnt, Fan (Cnt.add (Cnt.add (lowA (T i)).cnt (upA (T (i + 1))).cnt) m))
    (h0 : 0 < w → T 0 = true) : ∀ i, i < w → T i = true := by
  have hstep : ∀ i, i + 1 < w → T i = true → T (i + 1) = true := by
    intro i hi hT
    obtain ⟨m, hm⟩ := hmid i hi
    by_contra hF
    have : T (i + 1) = false := by simpa using hF
    rw [hT, this] at hm
    exact no_two_gamma _ _ m hm ⟨rfl, rfl⟩
  intro i hi
  induction i with
  | zero => exact h0 hi
  | succ k ih => exact hstep k hi (ih (by omega))

section row

variable {u v : ℕ} {α β γ L ax ay ε x : ℝ}

theorem row_orient_base (C : CtxBaseT D u v α β γ L ax ay ε x) (w : ℕ)
    (hnear : ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)))
    (hfar : ∀ i : ℕ, i < w → ∃ (t : Fin N) (k m : Fin 3), k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ))
    (hint : ∀ i : ℕ, i + 1 < w → lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∈ interior D.target.carrier)
    (hbase : 0 < w → ∀ (t : Fin N) (k m : Fin 3), k ≠ m →
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x (((0 : ℕ) : ℝ) + 1) (ηw w 0) →
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1) →
      (∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ)) →
      (D.tile t).localAngle (lpT (u : ℝ) (v : ℝ) ε x ((0 : ℕ) : ℝ) (ηw w 0 + 1)) = β) :
    ∀ i : ℕ, i < w → ∃ t, HasV D t (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i + 1)) := by
  have S := C.S
  have hε := C.e2
  have hlevel : ∀ i : ℕ, (i : ℝ) + ηw w i + 1 = (w : ℝ) := by intro i; unfold ηw; ring
  -- total choices
  have hN0 : 0 < N := D.pos
  have hnear' : ∀ i : ℕ, ∃ t : Fin N, i < w → HasV D t (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i))
      (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) := by
    intro i
    by_cases h : i < w
    · obtain ⟨t, ht⟩ := hnear i h; exact ⟨t, fun _ => ht⟩
    · exact ⟨⟨0, hN0⟩, fun h' => absurd h' h⟩
  have hfar' : ∀ i : ℕ, ∃ (t : Fin N) (k m : Fin 3), i < w → k ≠ m ∧
      (D.tile t).pts k = lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i) ∧
      (D.tile t).pts m = lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1) ∧
      ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile t).pts j) ≤ -lvT (u : ℝ) (v : ℝ) ε x (w : ℝ) := by
    intro i
    by_cases h : i < w
    · obtain ⟨t, k, m, hx⟩ := hfar i h; exact ⟨t, k, m, fun _ => hx⟩
    · exact ⟨⟨0, hN0⟩, 0, 0, fun h' => absurd h' h⟩
  choose nF hnF using hnear'
  choose tF kF mF hF using hfar'
  have hle' : ∀ i : ℕ, i < w → ∀ j, GST (u : ℝ) (v : ℝ) ε ((D.tile (tF i)).pts j)
      ≤ -lvT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + ηw w i + 1) := by
    intro i hi j
    rw [hlevel i]; exact (hF i hi).2.2.2 j
  -- the types
  have htype : ∀ i : ℕ, ∃ b : Bool, i < w →
      (D.tile (tF i)).localAngle (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) = angVal α (lowA b) ∧
      (D.tile (tF i)).localAngle (lpT (u : ℝ) (v : ℝ) ε x (i : ℝ) (ηw w i + 1)) = angVal α (upA b) := by
    intro i
    by_cases h : i < w
    · obtain ⟨hkm, hk, hm, -⟩ := hF i h
      obtain ⟨b, hb⟩ := far_type C hkm hk hm (hle' i h)
      exact ⟨b, fun _ => hb⟩
    · exact ⟨true, fun h' => absurd h' h⟩
  choose bF hbF using htype
  -- mid fans
  have hmid : ∀ i, i + 1 < w →
      ∃ m : Cnt, Fan (Cnt.add (Cnt.add (lowA (bF i)).cnt (upA (bF (i + 1))).cnt) m) := by
    intro i hi
    have hi' : i < w := by omega
    have e1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    have e2 : ηw w (i + 1) = ηw w i - 1 := by unfold ηw; push_cast; ring
    -- near tiles
    have hn1 := hnF i hi'
    have hn2' := hnF (i + 1) hi
    have hn2 : HasV D (nF (i + 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i - 1))
        (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 2) (ηw w i - 1)) (lpT (u : ℝ) (v : ℝ) ε x ((i : ℝ) + 1) (ηw w i)) :=
      hasV_congr hn2' (lpT_congr (by push_cast; ring) (by rw [e2]))
        (lpT_congr (by push_cast; ring) (by rw [e2]))
        (lpT_congr (by push_cast; ring) (by rw [e2]; ring))
    have heq : ((i + 1 : ℕ) : ℝ) + ηw w (i + 1) + 1 = (i : ℝ) + ηw w i + 1 := by
      rw [e2]; push_cast; ring
    refine vertexfan_T C (hint i hi) hn1 hn2 (tW := tF i) (tE := tF (i + 1))
      (hle' i hi') (fun j => by have := hle' (i + 1) hi j; rwa [heq] at this) ?_
      (lowA (bF i)) (upA (bF (i + 1))) ((hbF i hi').1) ?_
    · -- distinct far tiles
      obtain ⟨hkm, hk, hm, -⟩ := hF i hi'
      obtain ⟨hkm', hk', hm', -⟩ := hF (i + 1) hi
      refine far_ne_consec C hkm hk hm hkm' ?_ ?_
      · rw [hk']; exact lpT_congr (by push_cast; ring) (by rw [e2])
      · rw [hm']; exact lpT_congr (by push_cast; ring) (by rw [e2]; ring)
    · have := (hbF (i + 1) hi).2
      rw [← this]
      congr 1
      exact lpT_congr (by push_cast; ring) (by rw [e2]; ring)
  -- the base: the top far tile has `β` at `P`, hence is of type `D`
  have hT0 : 0 < w → bF 0 = true := by
    intro hw
    obtain ⟨hkm, hk, hm, -⟩ := hF 0 hw
    have hb := hbase hw (tF 0) (kF 0) (mF 0) hkm hk hm (hF 0 hw).2.2.2
    have hu := (hbF 0 hw).2
    rw [hb] at hu
    by_contra hfalse
    have hf : bF 0 = false := by simpa using hfalse
    rw [hf] at hu
    simp only [upA, angVal] at hu
    -- β = γ is impossible
    have h5 : (5 : ℝ) * α = Real.pi := by
      have : β = 2 * α := by simpa using hu
      rw [S.hβ] at this; linarith
    apply S.hirr
    refine ⟨(1 : ℚ) / 5, ?_⟩
    have : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
    push_cast
    field_simp
    linarith
  have hT := row_orient_comb' w bF hmid hT0
  intro i hi
  refine ⟨tF i, ?_⟩
  obtain ⟨hkm, hk, hm, -⟩ := hF i hi
  refine far_type_D C hkm hk hm (hle' i hi) ?_
  have := (hbF i hi).1
  rw [hT i hi] at this
  rw [this]; simp [lowA]

end row

#print axioms row_orient_base
end Erdos634.Draft.ThmDRun
