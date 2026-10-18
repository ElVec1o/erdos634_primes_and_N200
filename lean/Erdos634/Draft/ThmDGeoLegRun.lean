import Mathlib.Tactic
import Erdos634.Draft.ThmDLegPos

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1')): the tiles of a c-run of a positioned leg  

`LegEnd` : the local angle of the last tile at `B` is the right angle of its edge (the recursive form of the `hlast` conjunct of
`exists_chain_leg_pos`; `legEnd_of_last`).  `legpos_run`: if the first `n` edges of the leg are `c>` (`cp`, angles `(α, β)`), the
`i`-th tile has two vertices at the parameters `s + i c/|AB|`, `s + (i+1) c/|AB|` of `[A, B]` with local angles `α` and `β`
(`c = wlen model cp`).  With `ThmDGeoRun.hrun_of_tiles` this yields `hrun` of `lemmaK2_final`.
-/

namespace Erdos634.Draft.APrimeLegBuild

open Erdos634.Geometry Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg

/-- the last tile presents the right angle of its edge at `B` -/
def LegEnd {N : ℕ} (D : Dissection N) (α : ℝ) (B : Plane) : Fin N → OE → List (LegStep N) → Prop
  | t, e, [] => (D.tile t).localAngle B = angVal α e.r
  | _, _, st :: r => LegEnd D α B st.t st.e r

theorem legEnd_of_last {N : ℕ} (D : Dissection N) (α : ℝ) (B : Plane) :
    ∀ (r : List (LegStep N)) (t : Fin N) (e : OE),
      (D.tile (lastTile t r)).localAngle B = angVal α ((legEdges e r).getLast (List.cons_ne_nil _ _)).r →
      LegEnd D α B t e r := by
  intro r
  induction r with
  | nil => intro t e h; simpa [lastTile, legEdges] using h
  | cons st r ih =>
    intro t e h
    rw [getLast_legEdges_cons] at h
    exact ih st.t st.e (by simpa [lastTile] using h)

theorem legpos_run {N : ℕ} (D : Dissection N) (model : Tri) (α : ℝ) (A B : Plane) (c : ℝ)
    (hc : Erdos634.Draft.ThmD.wlen model OE.cp = c) (hAB : 0 < dist A B) :
    ∀ (i : ℕ) (r : List (LegStep N)) (t : Fin N) (e : OE) (s : ℝ),
      RealLeg D α t e r → LegPos D model A B t e s r → LegEnd D α B t e r →
      (D.tile t).localAngle (AffineMap.lineMap A B s) = angVal α e.l →
      (∀ j ≤ i, (legEdges e r)[j]? = some OE.cp) →
      ∃ (t' : Fin N) (j k : Fin 3), j ≠ k ∧
        (D.tile t').pts j = AffineMap.lineMap A B (s + i * (c / dist A B)) ∧
        (D.tile t').pts k = AffineMap.lineMap A B (s + (i + 1) * (c / dist A B)) ∧
        (D.tile t').localAngle ((D.tile t').pts j) = α ∧
        (D.tile t').localAngle ((D.tile t').pts k) = Real.pi - 3 * α := by
  intro i
  induction i with
  | zero =>
    intro r t e s hRL hLP hLE hang hcp
    have he : e = OE.cp := by
      have := hcp 0 le_rfl
      simpa [legEdges] using this
    subst he
    have hwl : Erdos634.Draft.ThmD.wlen model OE.cp = c := hc
    simp only [Nat.cast_zero, zero_mul, add_zero, zero_add, one_mul]
    cases r with
    | nil =>
      obtain ⟨j, k, hjk, hj, hk, hs, hl⟩ := hLP
      refine ⟨t, j, k, hjk, ?_, ?_, ?_, ?_⟩
      · exact hj
      · rw [hk]
        have : (1 : ℝ) = s + c / dist A B := by
          rw [hwl] at hl; field_simp; linarith
        rw [← this]
      · rw [hj, hang]; simp [OE.l, angVal]
      · rw [hk]
        have h := hLE
        simp only [LegEnd] at h
        rw [AffineMap.lineMap_apply_one, h]; simp [OE.r, angVal]
    | cons st r =>
      obtain ⟨s', j, k, hjk, hj, hk, hs, hs1, hp, hl, hLP'⟩ := hLP
      obtain ⟨hf, hnv, hne, hang1, hang2, hRL'⟩ := hRL
      have hs' : s' = s + c / dist A B := by
        rw [hwl] at hl; field_simp; linarith
      refine ⟨t, j, k, hjk, ?_, ?_, ?_, ?_⟩
      · exact hj
      · rw [hk, ← hs']
      · rw [hj, hang]; simp [OE.l, angVal]
      · rw [hk, ← hp, hang1]; simp [OE.r, angVal]
  | succ i ih =>
    intro r t e s hRL hLP hLE hang hcp
    have he : e = OE.cp := by
      have := hcp 0 (Nat.zero_le _)
      simpa [legEdges] using this
    subst he
    have hwl : Erdos634.Draft.ThmD.wlen model OE.cp = c := hc
    cases r with
    | nil =>
      have := hcp (i + 1) le_rfl
      simp [legEdges] at this
    | cons st r =>
      obtain ⟨s', j, k, hjk, hj, hk, hs, hs1, hp, hl, hLP'⟩ := hLP
      obtain ⟨hf, hnv, hne, hang1, hang2, hRL'⟩ := hRL
      have hs' : s' = s + (c / dist A B) := by
        rw [hwl] at hl; field_simp; linarith
      have hcp' : ∀ j ≤ i, (legEdges st.e r)[j]? = some OE.cp := by
        intro j hj
        have := hcp (j + 1) (by omega)
        simpa [legEdges] using this
      obtain ⟨t', j', k', h1, h2, h3, h4, h5⟩ := ih r st.t st.e s' hRL' hLP' hLE
        (by rw [← hp]; exact hang2) hcp'
      refine ⟨t', j', k', h1, ?_, ?_, h4, h5⟩
      · rw [h2, hs']; congr 1; push_cast; ring
      · rw [h3, hs']; congr 1; push_cast; ring



/-- **All tiles of a positioned leg with their parameters**: a function `f` of breakpoints, `f 0 = s`, `f (length) = 1`, the `idx`-th
tile has vertices at `f idx`, `f (idx+1)` with the local angles of the `idx`-th edge and `(f (idx+1) - f idx) |AB| = wlen`. -/
theorem legseq {N : ℕ} (D : Dissection N) (model : Tri) (α : ℝ) (A B : Plane) :
    ∀ (r : List (LegStep N)) (t : Fin N) (e : OE) (s : ℝ),
      RealLeg D α t e r → LegPos D model A B t e s r → LegEnd D α B t e r →
      (D.tile t).localAngle (AffineMap.lineMap A B s) = angVal α e.l →
      ∃ f : ℕ → ℝ, f 0 = s ∧ f (legEdges e r).length = 1 ∧
        ∀ idx (h : idx < (legEdges e r).length), ∃ (t' : Fin N) (j k : Fin 3), j ≠ k ∧
          (D.tile t').pts j = AffineMap.lineMap A B (f idx) ∧
          (D.tile t').pts k = AffineMap.lineMap A B (f (idx + 1)) ∧
          (D.tile t').localAngle ((D.tile t').pts j) = angVal α ((legEdges e r)[idx]).l ∧
          (D.tile t').localAngle ((D.tile t').pts k) = angVal α ((legEdges e r)[idx]).r ∧
          (f (idx + 1) - f idx) * dist A B = Erdos634.Draft.ThmD.wlen model ((legEdges e r)[idx]) := by
  intro r
  induction r with
  | nil =>
    intro t e s hRL hLP hLE hang
    obtain ⟨j, k, hjk, hj, hk, hs, hl⟩ := hLP
    refine ⟨fun i => if i = 0 then s else 1, by simp, by simp [legEdges], ?_⟩
    intro idx h
    have hidx : idx = 0 := by simpa [legEdges] using h
    subst hidx
    refine ⟨t, j, k, hjk, by simpa using hj, by simpa using hk, ?_, ?_, ?_⟩
    · rw [hj, hang]; simp [legEdges]
    · rw [hk]
      have h' := hLE
      simp only [LegEnd] at h'
      rw [AffineMap.lineMap_apply_one, h']; simp [legEdges]
    · simpa [legEdges] using hl.symm
  | cons st r ih =>
    intro t e s hRL hLP hLE hang
    obtain ⟨s', j, k, hjk, hj, hk, hs, hs1, hp, hl, hLP'⟩ := hLP
    obtain ⟨hf, hnv, hne, hang1, hang2, hRL'⟩ := hRL
    obtain ⟨f, hf0, hfl, hfi⟩ := ih st.t st.e s' hRL' hLP' hLE (by rw [← hp]; exact hang2)
    refine ⟨fun i => if i = 0 then s else f (i - 1), by simp, ?_, ?_⟩
    · have : (legEdges e (st :: r)).length = (legEdges st.e r).length + 1 := by simp [legEdges]
      rw [this]; simpa using hfl
    · intro idx h
      cases idx with
      | zero =>
        refine ⟨t, j, k, hjk, by simpa using hj, ?_, ?_, ?_, ?_⟩
        · simp [hf0, hk]
        · rw [hj, hang]; simp [legEdges]
        · rw [hk, ← hp, hang1]; simp [legEdges]
        · simp [hf0]; simpa [legEdges] using hl.symm
      | succ i =>
        have hi : i < (legEdges st.e r).length := by simp [legEdges] at h ⊢; omega
        obtain ⟨t', j', k', h1, h2, h3, h4, h5, h6⟩ := hfi i hi
        have e1 : (legEdges e (st :: r))[i + 1] = (legEdges st.e r)[i] := by simp [legEdges]
        refine ⟨t', j', k', h1, ?_, ?_, ?_, ?_, ?_⟩
        · simpa using h2
        · simpa using h3
        · rw [e1]; exact h4
        · rw [e1]; exact h5
        · simp only [Nat.add_sub_cancel, add_eq_zero, one_ne_zero, and_false, if_false, e1]
          simpa using h6

#print axioms legpos_run
#print axioms legseq
end Erdos634.Draft.APrimeLegBuild
