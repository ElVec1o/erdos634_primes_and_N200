import Mathlib
import Erdos634.Draft.FDDShapes
import Erdos634.Draft.RSBSine
import Erdos634.Draft.LemmaCFinal
import Erdos634.Draft.ISUReduce

/-!
# RSB, part 2: from a REAL `CongruentDissection` to a corner-type triple and a shape.

For a tile `(α, β = π/3 − α, 2π/3)` with `α/π` irrational,
every corner of `ABC` has angle `m α + k π/3`, `(m,k)` realizable, the three corners
satisfy `Σ m = 0, Σ k = 3`, hence the corner-type triple is one of the eleven shapes.

Proved here, for an arbitrary `CongruentDissection N` (any `N`, reflections allowed, no hypothesis on
the target):

* `corner_pairs`  : `∃ p : Fin 3 → ℤ×ℤ`, `p i` realizable, `target.angleAt i = (p i).1·α + (p i).2·π/3`,
                    `Σ m = 0`, `Σ k = 3`.            (the real-dissection half of the realizability and corner-sum conditions)
* `corner_shape`  : `∃ s : Shape, ∃ σ : Perm (Fin 3), ∀ j, p (σ j) = s.triple j` -- the corner-type triple is
                    one of the table's eleven shapes (via `FDDShapes.shapes_complete`).
* `pair_unique`   : distinct pairs give distinct angles (`α` irrational).

The corner decomposition is `LemmaCFigures.corner_figure` (the vertex figure at each target corner),
the table is `FDDShapes`; nothing here uses primality or any hypothesis on `N`.
-/

open scoped Classical

namespace Erdos634.Draft.RSBCorner

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.FDDShapes
  Erdos634.Draft.LemmaCFigures Erdos634.Draft.ISUReduce Erdos634.Draft.RSBSine

variable {N : ℕ}

/-! ## Arithmetic -/

theorem realizable_of_counts (c : Fin 3 → ℕ) (u v : Fin 3 → ℤ)
    (huv : ∀ j, (u j = 1 ∧ v j = 0) ∨ (u j = -1 ∧ v j = 1) ∨ (u j = 0 ∧ v j = 2))
    (hc : 1 ≤ c 0 + c 1 + c 2) :
    Realizable (∑ j, (c j : ℤ) * u j, ∑ j, (c j : ℤ) * v j) := by
  simp only [Fin.sum_univ_three, Realizable]
  rcases huv 0 with ⟨a0, b0⟩ | ⟨a0, b0⟩ | ⟨a0, b0⟩ <;>
  rcases huv 1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ | ⟨a1, b1⟩ <;>
  rcases huv 2 with ⟨a2, b2⟩ | ⟨a2, b2⟩ | ⟨a2, b2⟩ <;>
  simp only [a0, b0, a1, b1, a2, b2] <;> omega

/-- Distinct pairs give distinct angles when `α ∉ ℚπ`. -/
theorem pair_unique {α : ℝ} (hα : IrrPi α) (m k m' k' : ℤ)
    (h : (m : ℝ) * α + k * (Real.pi / 3) = m' * α + k' * (Real.pi / 3)) : m = m' ∧ k = k' := by
  have hpi := Real.pi_pos
  have h1 : ((m - m' : ℤ) : ℝ) * α = ((k' - k : ℤ) : ℝ) * (Real.pi / 3) := by
    push_cast; linarith
  have hm : m = m' := by
    by_contra hne
    have hne' : ((m - m' : ℤ) : ℝ) ≠ 0 := by
      intro h0; apply hne; have : (m - m' : ℤ) = 0 := by exact_mod_cast h0
      omega
    have hden : (3 * ((m - m' : ℤ) : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hne'
    refine hα ⟨((k' - k : ℤ) : ℚ) / (3 * ((m - m' : ℤ) : ℚ)), ?_⟩
    have hcast : ((((k' - k : ℤ) : ℚ) / (3 * ((m - m' : ℤ) : ℚ)) : ℚ) : ℝ)
        = ((k' - k : ℤ) : ℝ) / (3 * ((m - m' : ℤ) : ℝ)) := by push_cast; ring
    rw [hcast, div_mul_eq_mul_div, eq_div_iff hden]
    linarith
  refine ⟨hm, ?_⟩
  subst hm
  have h2 : ((k' - k : ℤ) : ℝ) * (Real.pi / 3) = 0 := by
    push_cast at h1 ⊢; linarith
  have : (k' - k : ℤ) = 0 := by
    have := (mul_eq_zero.mp h2).resolve_right (by positivity)
    exact_mod_cast this
  omega

/-- Three-element multiset equality gives a permutation of `Fin 3`. -/
theorem multiset3_perm {β : Type*} [DecidableEq β] (p t : Fin 3 → β)
    (h : ({p 0, p 1, p 2} : Multiset β) = {t 0, t 1, t 2}) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ j, p (σ j) = t j := by
  have aux2 : ∀ a b x y : β, ({a, b} : Multiset β) = {x, y} → (a = x ∧ b = y) ∨ (a = y ∧ b = x) := by
    intro a b x y hh
    have hx : x ∈ ({a, b} : Multiset β) := by rw [hh]; simp
    simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · left
      simp only [Multiset.insert_eq_cons, Multiset.cons_inj_right] at hh
      exact ⟨rfl, Multiset.singleton_inj.mp hh⟩
    · right
      rw [Multiset.pair_comm] at hh
      simp only [Multiset.insert_eq_cons, Multiset.cons_inj_right] at hh
      exact ⟨Multiset.singleton_inj.mp hh, rfl⟩
  have h0 : t 0 ∈ ({p 0, p 1, p 2} : Multiset β) := by rw [h]; simp
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at h0
  simp only [Multiset.insert_eq_cons] at h
  rcases h0 with e | e | e
  · -- t 0 = p 0
    rw [← e] at h
    simp only [Multiset.cons_inj_right] at h
    have h' : ({p 1, p 2} : Multiset β) = {t 1, t 2} := h
    rcases aux2 _ _ _ _ h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨1, fun j => ?_⟩
      fin_cases j
      · exact e.symm
      · exact e1
      · exact e2
    · refine ⟨LemmaCFinal.permOf 0 2 1 (by decide) (by decide) (by decide), fun j => ?_⟩
      fin_cases j
      · exact e.symm
      · exact e2
      · exact e1
  · -- t 0 = p 1
    have h2 : p 0 ::ₘ p 1 ::ₘ ({p 2} : Multiset β) = p 1 ::ₘ p 0 ::ₘ ({p 2} : Multiset β) :=
      Multiset.cons_swap _ _ _
    rw [h2, ← e] at h
    simp only [Multiset.cons_inj_right] at h
    have h' : ({p 0, p 2} : Multiset β) = {t 1, t 2} := h
    rcases aux2 _ _ _ _ h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨LemmaCFinal.permOf 1 0 2 (by decide) (by decide) (by decide), fun j => ?_⟩
      fin_cases j
      · exact e.symm
      · exact e1
      · exact e2
    · refine ⟨LemmaCFinal.permOf 1 2 0 (by decide) (by decide) (by decide), fun j => ?_⟩
      fin_cases j
      · exact e.symm
      · exact e2
      · exact e1
  · -- t 0 = p 2
    have h2 : p 0 ::ₘ p 1 ::ₘ ({p 2} : Multiset β) = p 2 ::ₘ p 0 ::ₘ ({p 1} : Multiset β) := by
      have : (p 1 ::ₘ ({p 2} : Multiset β)) = p 2 ::ₘ ({p 1} : Multiset β) := Multiset.cons_swap _ _ _
      rw [this]; exact Multiset.cons_swap _ _ _
    rw [h2, ← e] at h
    simp only [Multiset.cons_inj_right] at h
    have h' : ({p 0, p 1} : Multiset β) = {t 1, t 2} := h
    rcases aux2 _ _ _ _ h' with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · refine ⟨LemmaCFinal.permOf 2 0 1 (by decide) (by decide) (by decide), fun j => ?_⟩
      fin_cases j
      · exact e.symm
      · exact e1
      · exact e2
    · refine ⟨LemmaCFinal.permOf 2 1 0 (by decide) (by decide) (by decide), fun j => ?_⟩
      fin_cases j
      · exact e.symm
      · exact e2
      · exact e1

/-! ## The real-dissection bridge -/

theorem model_pairs (D : CongruentDissection N) {α a b c : ℝ} (hm : D.model.TwoPiThreeData α a b c)
    (j : Fin 3) :
    ∃ u v : ℤ, ((u = 1 ∧ v = 0) ∨ (u = -1 ∧ v = 1) ∨ (u = 0 ∧ v = 2)) ∧
      D.model.angleAt j = u * α + v * (Real.pi / 3) := by
  rcases model_angle_mem D hm j with h | h | h
  · exact ⟨1, 0, Or.inl ⟨rfl, rfl⟩, by rw [h]; push_cast; ring⟩
  · exact ⟨-1, 1, Or.inr (Or.inl ⟨rfl, rfl⟩), by rw [h]; push_cast; ring⟩
  · exact ⟨0, 2, Or.inr (Or.inr ⟨rfl, rfl⟩), by rw [h]; push_cast; ring⟩

/-- **Corner types of a real dissection (`eq:realizable`, `eq:cornersum`).**  For any
`CongruentDissection` by a `2π/3` tile with `α ∉ ℚπ`: each target corner has angle `m α + k π/3` with
`(m,k)` realizable, and `Σ m = 0`, `Σ k = 3`. -/
theorem corner_pairs (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) :
    ∃ p : Fin 3 → ℤ × ℤ, (∀ i, Realizable (p i)) ∧
      (∀ i, D.target.angleAt i = (p i).1 * α + (p i).2 * (Real.pi / 3)) ∧
      (∑ i, (p i).1 = 0) ∧ (∑ i, (p i).2 = 3) := by
  have hpos : ∀ m, 0 < D.model.angleAt m := fun m => Erdos634.MarchFlank.cornerAngle_pos D.model m
  have hlt : ∀ m, D.model.angleAt m < Real.pi := fun m =>
    Erdos634.RouteOneVertexKill.cornerAngle_lt_pi D.model m
  have hne := model_angle_ne D hα hm
  have hmα : cornerAngle (D.model.pts 1) (D.model.pts 0) (D.model.pts 2) = D.model.angleAt 0 := rfl
  have hmβ : cornerAngle (D.model.pts 2) (D.model.pts 1) (D.model.pts 0) = D.model.angleAt 1 := rfl
  have hmγ : cornerAngle (D.model.pts 0) (D.model.pts 2) (D.model.pts 1) = D.model.angleAt 2 := rfl
  have hcorner := fun kk => corner_figure D (D.model.angleAt 0) (D.model.angleAt 1)
    (D.model.angleAt 2) hmα hmβ hmγ (hne 0 1 (by decide)) (hne 0 2 (by decide))
    (hne 1 2 (by decide)) (hpos 0) (hpos 1) (hpos 2) (hlt 0) (hlt 1) (hlt 2) kk
  choose u v huv hx using model_pairs D hm
  have key : ∀ kk : Fin 3, ∃ c : Fin 3 → ℕ, 1 ≤ c 0 + c 1 + c 2 ∧
      D.target.angleAt kk = (c 0 : ℝ) * D.model.angleAt 0 + (c 1 : ℝ) * D.model.angleAt 1
        + (c 2 : ℝ) * D.model.angleAt 2 := by
    intro kk
    obtain ⟨-, h1, h2⟩ := hcorner kk
    exact ⟨![_, _, _], by simpa using h2, by simpa using h1.symm⟩
  choose c hc1 hang using key
  refine ⟨fun kk => (∑ j, (c kk j : ℤ) * u j, ∑ j, (c kk j : ℤ) * v j), ?_, ?_, ?_⟩
  · intro kk; exact realizable_of_counts (c kk) u v huv (hc1 kk)
  · intro kk
    rw [hang kk, hx 0, hx 1, hx 2]
    simp only [Fin.sum_univ_three]; push_cast; ring
  · have hang' : ∀ kk, D.target.angleAt kk = (∑ j, (c kk j : ℤ) * u j : ℤ) * α
        + (∑ j, (c kk j : ℤ) * v j : ℤ) * (Real.pi / 3) := by
      intro kk
      rw [hang kk, hx 0, hx 1, hx 2]
      simp only [Fin.sum_univ_three]; push_cast; ring
    set M : ℤ := ∑ kk, ∑ j, (c kk j : ℤ) * u j with hM
    set K : ℤ := ∑ kk, ∑ j, (c kk j : ℤ) * v j with hK
    have hsum := D.target.angleAt_sum
    rw [hang' 0, hang' 1, hang' 2] at hsum
    have hMK : (M : ℝ) * α + (K : ℝ) * (Real.pi / 3) = Real.pi := by
      simp only [hM, hK, Fin.sum_univ_three]; push_cast at hsum ⊢
      simp only [Fin.sum_univ_three] at hsum; linarith
    have hpi := Real.pi_pos
    have hM0 : M = 0 := by
      by_contra hne0
      have hne' : (M : ℝ) ≠ 0 := by exact_mod_cast hne0
      refine hα ⟨((3 - K : ℤ) : ℚ) / (3 * (M : ℚ)), ?_⟩
      push_cast
      field_simp
      push_cast at hMK ⊢
      linarith
    have hK3 : K = 3 := by
      rw [hM0] at hMK
      have : ((K : ℝ) - 3) * Real.pi = 0 := by push_cast at hMK ⊢; linarith
      have h3 := (mul_eq_zero.mp this).resolve_right hpi.ne'
      have : (K : ℝ) = 3 := by linarith
      exact_mod_cast this
    exact ⟨by simpa [Fin.sum_univ_three] using hM0, by simpa [Fin.sum_univ_three] using hK3⟩

/-- **Corner-type triple of a real dissection is one of the eleven shapes (`sub:shapes`).** -/
theorem corner_shape (D : CongruentDissection N) {α a b c : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α a b c) :
    ∃ (s : Shape) (σ : Equiv.Perm (Fin 3)),
      ∀ j, D.target.angleAt (σ j) = (s.triple j).1 * α + (s.triple j).2 * (Real.pi / 3) := by
  obtain ⟨p, hr, hang, hsm, hsk⟩ := corner_pairs D hα hm
  obtain ⟨s, hs⟩ := shapes_complete (p 0) (p 1) (p 2) (hr 0) (hr 1) (hr 2)
    (by simpa [Fin.sum_univ_three] using hsm) (by simpa [Fin.sum_univ_three] using hsk)
  rw [triple_corners s] at hs
  obtain ⟨σ, hσ⟩ := multiset3_perm p s.triple hs
  refine ⟨s, σ, fun j => ?_⟩
  rw [hang (σ j), hσ j]

end Erdos634.Draft.RSBCorner

#print axioms Erdos634.Draft.RSBCorner.corner_pairs
#print axioms Erdos634.Draft.RSBCorner.corner_shape
#print axioms Erdos634.Draft.RSBCorner.pair_unique
