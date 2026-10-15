-- Draft/FluxCSimilar.lean: the corollary on tile-similar targets.  A tile-similar target of a
-- `2π/3` tile with `α ∉ ℚπ` forces `N = μ²`, so `N` is never prime.  Imported by `All`.
--
-- The arithmetic part rests on `InvariantProduct.tile_similar_not_prime`, which is only the shell
-- `N = M² → ¬Prime N`.  The geometric steps (`M_α = ±μ` from the boundary lemma, `N = μ²` from the
-- area equation) are `Row2.lemmaW_square` (Draft/FluxCRow2) once `π ∉ 2Λ` is shown for the `2π/3`
-- tile; that is the only new content here.
--
-- This concerns the `2π/3` tile, not the base-β prime branch.
import Erdos634.Draft.FluxCRow2
import Erdos634.Draft.FluxPaper

open scoped Classical

namespace Erdos634.Geometry

variable {N : ℕ}

/-- Every angle of a `2π/3` placement is `j·π/3 + k·α`. -/
theorem Tri.twoPiThree_angle_form {T : Tri} {α a b c : ℝ} (h : T.TwoPiThreeData α a b c)
    (i : Fin 3) : ∃ j k : ℤ, T.angleAt i = (j : ℝ) * (Real.pi / 3) + (k : ℝ) * α := by
  obtain ⟨σ, h0, -, h1, -, h2, -⟩ := h
  obtain ⟨m, rfl⟩ := σ.surjective i
  have hm : m = 0 ∨ m = 1 ∨ m = 2 := by fin_cases m <;> simp
  rcases hm with rfl | rfl | rfl
  · exact ⟨0, 1, by rw [h0]; push_cast; ring⟩
  · exact ⟨1, -1, by rw [h1]; push_cast; ring⟩
  · exact ⟨2, 0, by rw [h2]; push_cast; ring⟩

/-- **`π ∉ 2Λ` for the `2π/3` tile** (`Λ = ⟨θ₀, θ₁, π⟩ ⊆ ℤπ/3 + ℤα`, `α ∉ ℚπ`). -/
theorem Tri.twoPiThree_pi_not_two {T : Tri} {α a b c : ℝ} (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi)
    (h : T.TwoPiThreeData α a b c) :
    ∀ y ∈ AddSubgroup.closure ({T.angleAt 0, T.angleAt 1, Real.pi} : Set ℝ), Real.pi ≠ 2 * y := by
  have hform : ∀ y ∈ AddSubgroup.closure ({T.angleAt 0, T.angleAt 1, Real.pi} : Set ℝ),
      ∃ j k : ℤ, y = (j : ℝ) * (Real.pi / 3) + (k : ℝ) * α := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem x hx =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact T.twoPiThree_angle_form h 0
      · exact T.twoPiThree_angle_form h 1
      · exact ⟨3, 0, by push_cast; ring⟩
    | zero => exact ⟨0, 0, by push_cast; ring⟩
    | add x y _ _ hx hy =>
      obtain ⟨j, k, rfl⟩ := hx
      obtain ⟨j', k', rfl⟩ := hy
      exact ⟨j + j', k + k', by push_cast; ring⟩
    | neg x _ hx =>
      obtain ⟨j, k, rfl⟩ := hx
      exact ⟨-j, -k, by push_cast; ring⟩
  intro y hy hpi
  obtain ⟨j, k, rfl⟩ := hform y hy
  by_cases hk : k = 0
  · subst hk
    have h1 : ((3 : ℝ) - 2 * j) * Real.pi = 0 := by push_cast at hpi; linear_combination 3 * hpi
    have h2 : (3 : ℝ) - 2 * j = 0 := (mul_eq_zero.mp h1).resolve_right Real.pi_ne_zero
    have h3 : (3 : ℤ) = 2 * j := by exact_mod_cast (by linarith : (3 : ℝ) = 2 * j)
    omega
  · apply hα
    have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
    refine ⟨((3 - 2 * j : ℤ) : ℚ) / ((6 * k : ℤ) : ℚ), ?_⟩
    push_cast
    rw [div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (by norm_num) hk')]
    linear_combination (-3 : ℝ) * hpi

/-- **`cor:similar`, geometric form.**  For an `N`-tiling by a `2π/3` tile with `α ∉ ℚπ` of a target
similar to the model with ratio `μ` (same vertex order; reflections allowed), `N = m²` with `m = μ`,
and `N` is not prime. -/
theorem Paper.cor_similar (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k
      ∧ D.target.oppLen k = μ * D.model.oppLen k) :
    ∃ m : ℕ, N = m ^ 2 ∧ μ = m ∧ ¬ N.Prime := by
  have hπ := D.model.twoPiThree_pi_not_two hα h
  obtain ⟨m, hm, hμ⟩ := Row2.lemmaW_square D μ hsim hπ
  exact ⟨m, hm, hμ, Row2.lemmaW_not_prime D μ hsim hπ⟩

/-- **`cor:similar` as printed: `N = M_α²`**, with `M_α` the integer of `cor:int`
(`Φ_{f_α}(∂ABC) = M_α (c + a − b)`); hence `N` is a perfect square and never prime. -/
theorem Paper.cor_similar_Malpha (D : CongruentDissection N) {α a b c μ : ℝ}
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (h : D.model.TwoPiThreeData α a b c)
    (hsim : ∀ k, D.target.angleAt k = D.model.angleAt k
      ∧ D.target.oppLen k = μ * D.model.oppLen k) :
    ∃ Mα : ℤ, D.target.flux (fAlpha α hα).weight = (Mα : ℝ) * (c + a - b) ∧
      (N : ℤ) = Mα ^ 2 ∧ ¬ N.Prime := by
  obtain ⟨Mα, -, -, -, hMα, -⟩ := Paper.cor_int D hα h
  obtain ⟨m, hm, hμ, hp⟩ := Paper.cor_similar D hα h hsim
  have hsq := GridChar.rankn_sq 3 (by norm_num) (by decide) α hα 0 0
  have hmodel := D.model.data_angles_mem hα h 0
  have htarget : ∀ k, ((D.target.angleAt k : ℝ) : Real.Angle) ∈ (fAlpha α hα).L := fun k => by
    rw [(hsim k).1]; exact hmodel k
  have hKt : (fAlpha α hα).tileValue D.target = μ * (fAlpha α hα).tileValue D.model := by
    unfold GridChar.tileValue
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hsim k).1, (hsim k).2]
    ring
  have hKm : (fAlpha α hα).tileValue D.model = -(c + a - b) := data_tileValue_alpha D.model hα h
  have hK0 : c + a - b ≠ 0 := by
    have := (fAlpha α hα).tileValue_ne_zero hsq D.model hmodel
    rw [hKm] at this
    exact fun h0 => this (by rw [h0, neg_zero])
  have hM2 : (Mα : ℝ) ^ 2 = μ ^ 2 := by
    rcases D.target.flux_grid_pm (fAlpha α hα) hsq htarget with e | e
    · rw [hMα, hKt, hKm] at e
      have : (Mα : ℝ) = -μ := mul_right_cancel₀ hK0 (by linear_combination e)
      rw [this]; ring
    · rw [hMα, hKt, hKm] at e
      have : (Mα : ℝ) = μ := mul_right_cancel₀ hK0 (by linear_combination e)
      rw [this]
  refine ⟨Mα, hMα, ?_, hp⟩
  have : ((N : ℤ) : ℝ) = ((Mα ^ 2 : ℤ) : ℝ) := by
    push_cast
    rw [hM2, hμ, hm]
    push_cast
    ring
  exact_mod_cast this

end Erdos634.Geometry

#print axioms Erdos634.Geometry.Tri.twoPiThree_pi_not_two
#print axioms Erdos634.Geometry.Paper.cor_similar
#print axioms Erdos634.Geometry.Paper.cor_similar_Malpha
