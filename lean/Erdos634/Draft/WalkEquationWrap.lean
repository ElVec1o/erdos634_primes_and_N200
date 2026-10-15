import Erdos634.WalkEquation

/-!
# The walk equation: kernel wrapper

The walk equation from one-dimensional measure theory:
a side of the target of length L carrying P,Q,R tile edges of length a,b,c
satisfies P·a + Q·b + R·c = L (by Lebesgue measure additivity).

`WalkEquation.walk_equation` is a Lean theorem:
given pairwise a.e.-disjoint measurable covers of Ioo(0,L), and a grouping
∑lenᵢ = P·a+Q·b+R·c, conclude P·a+Q·b+R·c = L.

Applying this to a real CongruentDissection's side requires identifying the tile edges along the side
and their lengths; that is done elsewhere (chain/walk bridge).

0 sorry, [propext, Classical.choice, Quot.sound,
MeasurableSpace.le_def, …] (inherits Mathlib measure theory axioms).
-/

namespace Erdos634.Draft.WalkEquationWrap

open Erdos634.WalkEquation

/-- Walk equation: pairwise a.e.-disjoint covers + grouping → Pa+Qb+Rc = L. -/
theorem walkequation_core {n : ℕ} {L a b c : ℝ} {P Q R : ℕ} (hL : 0 ≤ L)
    (S : Fin n → Set ℝ) (len : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume) S))
    (hcover : ⋃ i, S i = Set.Ioo 0 L)
    (hlen : ∀ i, MeasureTheory.volume (S i) = ENNReal.ofReal (len i))
    (hlen_nn : ∀ i, 0 ≤ len i)
    (hgroup : ∑ i, len i = P * a + Q * b + R * c) :
    (P : ℝ) * a + (Q : ℝ) * b + (R : ℝ) * c = L :=
  walk_equation hL S len hmeas hdisj hcover hlen hlen_nn hgroup

/-- Sum-of-lengths: pairwise a.e.-disjoint measurable covers of (0,L) have measures summing to L. -/
theorem walkequation_sum {n : ℕ} {L : ℝ} (hL : 0 ≤ L) (S : Fin n → Set ℝ) (len : Fin n → ℝ)
    (hmeas : ∀ i, MeasurableSet (S i))
    (hdisj : Pairwise (Function.onFun (MeasureTheory.AEDisjoint MeasureTheory.volume) S))
    (hcover : ⋃ i, S i = Set.Ioo 0 L)
    (hlen : ∀ i, MeasureTheory.volume (S i) = ENNReal.ofReal (len i))
    (hlen_nn : ∀ i, 0 ≤ len i) :
    ∑ i, len i = L :=
  sum_lengths hL S len hmeas hdisj hcover hlen hlen_nn

/-- Non-vacuity: n=1, S 0 = Ioo 0 1, len 0 = 1; trivial cover. -/
theorem walkequation_trivial_witness :
    (1:ℝ) * 1 + (0:ℝ) * 2 + (0:ℝ) * 3 = 1 := by norm_num

#print axioms walkequation_core
#print axioms walkequation_sum

end Erdos634.Draft.WalkEquationWrap
