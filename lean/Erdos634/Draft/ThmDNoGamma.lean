import Erdos634.Draft.APrimeLegBuild

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha is ours.

# Theorem D' (ThmDGeo, item (1)): no `γ` at a target corner  

`no_gamma_at_corner`: in a dissection by tiles `(α, π-3α, 2α)` with `α/π` irrational, no tile has local angle `γ = 2α` at a target vertex
whose corner angle is `α` or `π - 2α` (the corners of `T(g)`).  This is the standing hypothesis `hnoγ` of `lemmaK2_final`, for the
three vertices of the target.  Proof: `corner_total` leaves a natural combination `X α + Y β + Z γ` and the irrationality of `α/π`
(coefficient of `π`) forces `Y = 0` resp. `Y = 1`, a contradiction in the `α` coefficient.
-/

namespace Erdos634.Draft.ThmD

open Erdos634.Geometry Erdos634.Draft.APrimeLeg Erdos634.Draft.APrimeLegBuild

theorem lin_irr {α : ℝ} (hirr : Irrational (α / Real.pi)) (p q : ℤ)
    (h : (p : ℝ) * α + (q : ℝ) * Real.pi = 0) : p = 0 ∧ q = 0 := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  by_cases hp : p = 0
  · subst hp
    have : (q : ℝ) * Real.pi = 0 := by simpa using h
    have hq : (q : ℝ) = 0 := (mul_eq_zero.mp this).resolve_right hpi
    exact ⟨rfl, by exact_mod_cast hq⟩
  · exfalso
    apply hirr
    refine ⟨(-q : ℚ) / p, ?_⟩
    have hp' : (p : ℝ) ≠ 0 := by exact_mod_cast hp
    push_cast
    rw [div_eq_div_iff hp' hpi]
    linarith

/-- no `γ` at a corner of angle `α` or `π - 2α`. -/
theorem no_gamma_at_corner {N : ℕ} (D : Dissection N) (model : Tri)
    (hcong : ∀ i, model.Congruent (D.tile i)) {α : ℝ} (hirr : Irrational (α / Real.pi))
    (hA0 : cornerAngle (model.pts 1) (model.pts 0) (model.pts 2) = α)
    (hA1 : cornerAngle (model.pts 2) (model.pts 1) (model.pts 0) = Real.pi - 3 * α)
    (hA2 : cornerAngle (model.pts 0) (model.pts 2) (model.pts 1) = 2 * α)
    (hα : 0 < α) (h3 : 3 * α < Real.pi)
    (k : Fin 3)
    (hc : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α ∨
          cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = Real.pi - 2 * α)
    (t : Fin N) : (D.tile t).localAngle (D.target.pts k) ≠ 2 * α := by
  intro h
  have hcpi : ∀ c, (c = α ∨ c = Real.pi - 2 * α) → c < Real.pi := by
    intro c hc'; rcases hc' with rfl | rfl <;> linarith
  rcases hc with hc | hc
  · obtain ⟨X, Y, Z, hXYZ⟩ := corner_total D model hcong α hA0 hA1 hA2 k _ hc (hcpi _ (Or.inl rfl)) t .ga
      (by simpa [angVal] using h)
    simp only [angVal] at hXYZ
    have hint := lin_irr hirr ((X : ℤ) + 2 * Z - 3 * Y + 1) (Y : ℤ) (by push_cast; linarith)
    omega
  · obtain ⟨X, Y, Z, hXYZ⟩ := corner_total D model hcong α hA0 hA1 hA2 k _ hc (hcpi _ (Or.inr rfl)) t .ga
      (by simpa [angVal] using h)
    simp only [angVal] at hXYZ
    have hint := lin_irr hirr ((X : ℤ) + 2 * Z - 3 * Y + 4) ((Y : ℤ) - 1) (by push_cast; linarith)
    omega

#print axioms no_gamma_at_corner
end Erdos634.Draft.ThmD
