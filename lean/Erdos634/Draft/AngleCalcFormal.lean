-- Draft/AngleCalcFormal.lean: the angle calculus as theorems about REAL angles.
-- The five clauses of the angle calculus, first in the paper's own encoding (α↦(1,0), β↦(0,1),
-- γ↦(2,1), π↦(3,2); `AngleArithmetic`, all five bundled), then for real angles `α, β` with
-- `3α+2β = π` and `α ∉ ℚπ` ("for every member (e,f)": `α ∉ ℚπ` is supplied at every member by
-- `BaseBetaE1.tile_alpha_irrational`, Niven).  Clause (1) ("π/2 has no representation") needs `α ∉ ℚπ`
-- and `3α+2β=π`: it fails for α = π/6 (β = π/4: π/2 = 2β).  `AngleArithmetic.no_right_angle` is the
-- arithmetic AFTER representation uniqueness; the real-angle form is stated here.
import Erdos634.AngleArithmetic
import Erdos634.Dissection
import Erdos634.BaseBetaE1
import Erdos634.TileAt
import Erdos634.CornerBaseEdgesReal

namespace Erdos634.Draft.AngleCalcFormal

open Erdos634.Geometry

/-- **`lem:anglecalc`, in the paper's encoding.**  A vertex figure with `na` α's, `nb` β's, `ng` γ's
at an angle `(X,Y)` solves `na + 2 ng = X`, `nb + ng = Y`. -/
theorem lem_anglecalc_arith :
    (∀ x y : Nat, ¬ (2 * x = 3 ∧ 2 * y = 2)) ∧
    (∀ na nb ng : Nat, na + 2 * ng = 3 → nb + ng = 0 → na = 3 ∧ nb = 0 ∧ ng = 0) ∧
    (∀ na nb ng : Nat, na + 2 * ng = 0 → nb + ng = 1 → na = 0 ∧ nb = 1 ∧ ng = 0) ∧
    (∀ na nb ng : Nat, na + 2 * ng = 3 → nb + ng = 2 →
        ((na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1)) ∧ ng ≤ 1) ∧
    (∀ na nb ng : Nat, na + 2 * ng = 1 → nb + ng = 1 → na = 1 ∧ nb = 1 ∧ ng = 0) :=
  ⟨Erdos634.AngleArithmetic.no_right_angle, Erdos634.AngleArithmetic.apex_forced,
    Erdos634.AngleArithmetic.beta_corner_forced,
    fun na nb ng hx hy => ⟨Erdos634.AngleArithmetic.pi_vertex na nb ng hx hy,
      Erdos634.AngleArithmetic.gamma_trap na nb ng hx hy⟩,
    Erdos634.AngleArithmetic.alpha_beta_corner⟩

/-- **`lem:anglecalc` for real angles.**  With `3α+2β = π`, `α ∉ ℚπ` and `γ = 2α+β`:
(1) `π/2` is not `xα + yβ`; (2) at the apex `3α` the only figure is three `α`'s; (3) at an angle `β`
the only figure is one `β`; (4) at a straight angle `π` the only figures are `{ααα,ββ}` and
`{γ,α,β}`, and at most one `γ`; (5) at `α+β` the only figure is one `α` and one `β`. -/
theorem lem_anglecalc_real {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    (¬ ∃ x y : ℕ, (x : ℝ) * α + (y : ℝ) * β = Real.pi / 2) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 3 * α →
        x = 3 ∧ y = 0 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = β →
        x = 0 ∧ y = 1 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = Real.pi →
        ((x = 3 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1)) ∧ z ≤ 1) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = α + β →
        x = 1 ∧ y = 1 ∧ z = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨x, y, h⟩
    obtain ⟨h1, h2⟩ := vertex_multiplicities hrel hirr (2 * x) (2 * y) 0 3 2
      (by push_cast; linarith)
    push_cast at h1 h2
    omega
  · intro x y z h
    obtain ⟨h1, h2⟩ := vertex_apex_multiplicities hrel hirr x y z h
    exact Erdos634.BaseBetaE1.vertex_apex x y z h1 h2
  · intro x y z h
    obtain ⟨h1, h2⟩ := vertex_beta_corner_multiplicities hrel hirr x y z h
    exact Erdos634.BaseBetaE1.vertex_beta_corner x y z h1 h2
  · intro x y z h
    obtain ⟨h1, h2⟩ := vertex_pi_multiplicities hrel hirr x y z h
    exact ⟨Erdos634.BaseBetaE1.vertex_pi x y z h1 h2, by omega⟩
  · intro x y z h
    obtain ⟨h1, h2⟩ := vertex_multiplicities hrel hirr x y z 1 1 (by push_cast; linarith)
    exact Erdos634.AngleArithmetic.alpha_beta_corner x y z (by omega) (by omega)

/-- **`lem:anglecalc` for every member `(e,f)`** (`1 ≤ e < f`): the tile of the member has
`sin(α/2) = e/(2f)` and `3α+2β = π`; then `α ∉ ℚπ` (Niven) and the five clauses hold. -/
theorem lem_anglecalc_member (e f : ℕ) (he : 1 ≤ e) (hef : e < f) {α β : ℝ}
    (hrel : 3 * α + 2 * β = Real.pi) (hsin : Real.sin (α / 2) = (e : ℝ) / (2 * (f : ℝ))) :
    (¬ ∃ x y : ℕ, (x : ℝ) * α + (y : ℝ) * β = Real.pi / 2) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 3 * α →
        x = 3 ∧ y = 0 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = β →
        x = 0 ∧ y = 1 ∧ z = 0) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = Real.pi →
        ((x = 3 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1)) ∧ z ≤ 1) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = α + β →
        x = 1 ∧ y = 1 ∧ z = 0) :=
  lem_anglecalc_real hrel (Erdos634.BaseBetaE1.tile_alpha_irrational e f he hef α hsin)

/-- **"The only figures are …" is an equivalence** (the paper: "a vertex figure at an angle `(X,Y)` is
*exactly* a solution of `n_α + 2n_γ = X`, `n_β + n_γ = Y`"): the figures named in clauses (2)-(5) are
solutions, and the solutions are exactly those. -/
theorem lem_anglecalc_iff :
    (∀ na nb ng : Nat, (na + 2 * ng = 3 ∧ nb + ng = 0) ↔ (na = 3 ∧ nb = 0 ∧ ng = 0)) ∧
    (∀ na nb ng : Nat, (na + 2 * ng = 0 ∧ nb + ng = 1) ↔ (na = 0 ∧ nb = 1 ∧ ng = 0)) ∧
    (∀ na nb ng : Nat, (na + 2 * ng = 3 ∧ nb + ng = 2) ↔
        ((na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1))) ∧
    (∀ na nb ng : Nat, (na + 2 * ng = 1 ∧ nb + ng = 1) ↔ (na = 1 ∧ nb = 1 ∧ ng = 0)) := by
  refine ⟨fun na nb ng => ?_, fun na nb ng => ?_, fun na nb ng => ?_, fun na nb ng => ?_⟩ <;>
    omega

/-- The same equivalences for real angles: the named figures really do sum to the angle. -/
theorem lem_anglecalc_real_iff {α β : ℝ} (hrel : 3 * α + 2 * β = Real.pi)
    (hirr : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) :
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = 3 * α ↔
        (x = 3 ∧ y = 0 ∧ z = 0)) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = β ↔
        (x = 0 ∧ y = 1 ∧ z = 0)) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = Real.pi ↔
        ((x = 3 ∧ y = 2 ∧ z = 0) ∨ (x = 1 ∧ y = 1 ∧ z = 1))) ∧
    (∀ x y z : ℕ, (x : ℝ) * α + (y : ℝ) * β + (z : ℝ) * (2 * α + β) = α + β ↔
        (x = 1 ∧ y = 1 ∧ z = 0)) := by
  obtain ⟨-, h2, h3, h4, h5⟩ := lem_anglecalc_real hrel hirr
  refine ⟨fun x y z => ⟨h2 x y z, ?_⟩, fun x y z => ⟨h3 x y z, ?_⟩,
    fun x y z => ⟨fun h => (h4 x y z h).1, ?_⟩, fun x y z => ⟨h5 x y z, ?_⟩⟩
  · rintro ⟨rfl, rfl, rfl⟩; push_cast; ring
  · rintro ⟨rfl, rfl, rfl⟩; push_cast; ring
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩) <;> push_cast <;> linarith
  · rintro ⟨rfl, rfl, rfl⟩; push_cast; ring

/-- Counterexample for clause (1): the hypothesis `α ∉ ℚπ` is load-bearing.  With `α = π/6`,
`β = π/4` (`3α + 2β = π`) one has `π/2 = 0·α + 2·β`. -/
theorem clause1_needs_irrationality :
    ∃ α β : ℝ, 3 * α + 2 * β = Real.pi ∧ (∃ r : ℚ, α = (r : ℝ) * Real.pi) ∧
      ∃ x y : ℕ, (x : ℝ) * α + (y : ℝ) * β = Real.pi / 2 :=
  ⟨Real.pi / 6, Real.pi / 4, by ring, ⟨1 / 6, by push_cast; ring⟩, 0, 2, by push_cast; ring⟩

end Erdos634.Draft.AngleCalcFormal

#print axioms Erdos634.Draft.AngleCalcFormal.lem_anglecalc_arith
#print axioms Erdos634.Draft.AngleCalcFormal.lem_anglecalc_real
#print axioms Erdos634.Draft.AngleCalcFormal.lem_anglecalc_member
#print axioms Erdos634.Draft.AngleCalcFormal.clause1_needs_irrationality
#print axioms Erdos634.Draft.AngleCalcFormal.lem_anglecalc_iff
#print axioms Erdos634.Draft.AngleCalcFormal.lem_anglecalc_real_iff
-- the cited rider theorems (existing, in TileAt / CornerBaseEdgesReal):
#print axioms Erdos634.Geometry.Dissection.congruentDissection_no_double_gamma
#print axioms Erdos634.Geometry.Dissection.congruentDissection_apex_counts
#print axioms Erdos634.Geometry.Dissection.congruentDissection_base_corner_counts
#print axioms Erdos634.CornerBaseEdgesReal.congruentDissection_base_corner_edges
