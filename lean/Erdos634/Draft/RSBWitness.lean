import Mathlib
import Erdos634.Draft.RSBArea
import Erdos634.Draft.RSBReduce
import Erdos634.Draft.ADMControl
import Erdos634.Draft.FluxPaperWitness

/-!
# RSB, part 5: witnesses and wrong-shape checks for `RSBArea.bridge`.

* `w2673`: the REAL certified 2673-tile tiling (`G3CIsoControl.D`, tile `1890·(3,5,7)`, target
  `1890·(189,189,297)`): every hypothesis of `bridge` holds; the conclusion evaluates to shape `isoBeta`,
  `k = 27`, `2673·3 = 27²·11`.
* `w357`: the REAL scalene-corpus tiling `FluxPaperWitness.D357` (`N = 4`, the scale-2 ladder of the `(3,5,7)`
  tile, target the homothetic copy): shape `tileSimilar`, `k = 2`, `4 = 2²`.
* wrong shapes: the same data do NOT admit the wrong shapes; e.g. `¬ ∃ k, isoAlpha.AreaEq 3 5 k 2673`
  (so the table's `AreaEq` clause discriminates), and `¬` any shape other than `tileSimilar` solves the
  `N = 4` equation.
-/

open scoped Classical

namespace Erdos634.Draft.RSBWitness

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.FDDShapes
  Erdos634.Draft.RSBSine Erdos634.Draft.RSBCorner Erdos634.Draft.RSBArea

/-! ### N = 2673 -/

section W2673

open Erdos634.Draft.G3CIsoControl

theorem w2673 : ∃ (σ : Equiv.Perm (Fin 3)) (k : ℕ), k = 27 ∧
    (∀ j, D.target.angleAt (σ j) = (Shape.isoBeta.triple j).1 * α
      + (Shape.isoBeta.triple j).2 * (Real.pi / 3)) ∧
    (∀ j, D.target.oppLen (σ j) = 1890 * k * (Shape.isoBeta.sideV 3 5 7 j)) := by
  obtain ⟨s, σ, k, hk, hang, hside, harea⟩ :=
    bridge D (K := 1890) (by norm_num) 3 5 7 (by norm_num) (by norm_num) α_irr
      Erdos634.Draft.ADMControl.hm3
  have hmem : ∀ j, s.triple j = (-1, 1) ∨ s.triple j = (2, 1) := by
    intro j
    obtain ⟨τ, h0, h1, h2⟩ := Erdos634.Draft.ADMControl.tgt_beta
    obtain ⟨i, hi⟩ := τ.surjective (σ j)
    have hj := hang j
    rw [← hi] at hj
    have hpair : ∀ m k : ℤ, (m : ℝ) * α + k * (Real.pi / 3) = D.target.angleAt (τ i) →
        s.triple j = (m, k) := by
      intro m k hmk
      rw [hj] at hmk
      obtain ⟨e1, e2⟩ := pair_unique α_irr _ _ _ _ hmk
      exact Prod.ext e1.symm e2.symm
    fin_cases i
    · left
      refine hpair (-1) 1 ?_
      show _ = D.target.angleAt (τ 0)
      rw [h0]; push_cast; ring
    · left
      refine hpair (-1) 1 ?_
      show _ = D.target.angleAt (τ 1)
      rw [h1]; push_cast; ring
    · right
      refine hpair 2 1 ?_
      show _ = D.target.angleAt (τ 2)
      rw [h2]; push_cast; ring
  have hs : s = Shape.isoBeta := by
    have key : ∀ s : Shape, (∀ j, s.triple j = (-1, 1) ∨ s.triple j = (2, 1)) → s = .isoBeta := by
      decide
    exact key s hmem
  subst hs
  have hN := G3CIso2673.cert_len
  unfold Shape.AreaEq at harea
  rw [hN] at harea
  simp only [Shape.den, Shape.num] at harea
  have hk27 : k = 27 := by
    have : k ≤ 28 := by nlinarith
    interval_cases k <;> omega
  exact ⟨σ, k, hk27, hang, hside⟩

/-- **Wrong shape fails.**  On the same data `(a,b,N) = (3,5,2673)` the `isoAlpha` area equation has no
solution (`2673·5 = 13365 = 13·k²` is impossible), so `AreaEq` rules shapes out on a real tiling. -/
theorem control_isoAlpha : ¬ ∃ k : ℕ, Shape.isoAlpha.AreaEq 3 5 k 2673 := by
  rintro ⟨k, hk⟩
  unfold Shape.AreaEq at hk
  simp only [Shape.den, Shape.num] at hk
  have : k ≤ 40 := by nlinarith
  interval_cases k <;> omega

/-- The only shapes admitting an area equation at `(a,b,N) = (3,5,2673)` are `isoBeta` and (nothing
else): a full sweep of the table. -/
theorem control_only_isoBeta : ∀ s : Shape, (∃ k : ℕ, 0 < k ∧ s.AreaEq 3 5 k 2673) →
    s = .isoBeta := by
  intro s ⟨k, hk, h⟩
  unfold Shape.AreaEq at h
  have hk' : k ≤ 201 := by
    cases s <;> simp only [Shape.den, Shape.num] at h <;> nlinarith
  cases s <;> simp only [Shape.den, Shape.num] at h <;> first | rfl | (interval_cases k <;> omega)

end W2673

/-! ### N = 4 (scalene corpus tiling) -/

section W357

open Erdos634.Draft.FluxPaperWitness

theorem hm357 : D357.model.TwoPiThreeData α357 (1 * ((3 : ℕ) : ℝ)) (1 * ((5 : ℕ) : ℝ))
    (1 * ((7 : ℕ) : ℝ)) := by
  have := data357
  simpa using this

theorem w357 : ∃ (s : Shape) (σ : Equiv.Perm (Fin 3)) (k : ℕ), s = .tileSimilar ∧ k = 2 ∧
    (∀ j, D357.target.angleAt (σ j) = (s.triple j).1 * α357 + (s.triple j).2 * (Real.pi / 3)) ∧
    (∀ j, D357.target.oppLen (σ j) = 1 * k * (s.sideV 3 5 7 j)) := by
  obtain ⟨s, σ, k, hk, hang, hside, harea⟩ :=
    bridge D357 (K := 1) (by norm_num) 3 5 7 (by norm_num) (by norm_num) α357_irr hm357
  have key : ∀ s : Shape, ∀ k : ℕ, 0 < k → s.AreaEq 3 5 k (2 * 2) → s = .tileSimilar ∧ k = 2 := by
    intro s k hk h
    unfold Shape.AreaEq at h
    have hk' : k ≤ 30 := by
      cases s <;> simp only [Shape.den, Shape.num] at h <;> nlinarith
    cases s <;> simp only [Shape.den, Shape.num] at h <;>
      first | exact ⟨rfl, by interval_cases k <;> omega⟩ | (exfalso; interval_cases k <;> omega)
  obtain ⟨hs, hk2⟩ := key s k hk harea
  exact ⟨s, σ, k, hs, hk2, hang, hside⟩

/-- At `N = 4`: every shape except `tileSimilar` fails. -/
theorem control_357 : ∀ s : Shape, s ≠ .tileSimilar → ¬ ∃ k : ℕ, 0 < k ∧ s.AreaEq 3 5 k (2 * 2) := by
  intro s hs ⟨k, hk, h⟩
  unfold Shape.AreaEq at h
  have hk' : k ≤ 30 := by
    cases s <;> simp only [Shape.den, Shape.num] at h <;> nlinarith
  cases s <;> simp only [Shape.den, Shape.num] at h <;>
    first | exact hs rfl | (interval_cases k <;> omega)

end W357

#print axioms Erdos634.Draft.RSBWitness.w2673
#print axioms Erdos634.Draft.RSBWitness.control_isoAlpha
#print axioms Erdos634.Draft.RSBWitness.control_only_isoBeta
#print axioms Erdos634.Draft.RSBWitness.w357
#print axioms Erdos634.Draft.RSBWitness.control_357

end Erdos634.Draft.RSBWitness
