/-
Draft/ThresholdBlind.lean -- which invariants cannot exclude a scale below `f` on the base-β row.

A member `(e, f)` of the base-β row has a tiling at every scale `M ≥ f` (`Draft.Residue.betaTilable_ge`) and none at
`M = 1`.  Let `ι : ℕ → X` be any quantity attached to the scale that takes the value `z` at every scale with a tiling
(an "invariant": `ι M ≠ z` would exclude the scale `M`).  If `ι` is BACKWARD DETERMINISTIC (the value `z` at all
later scales forces the value `z`), then `ι M = z` at EVERY scale, the scale `1` included: such an invariant excludes
nothing.

    theorem blind_of_backward   : backward deterministic, `= z` from `f` on   →  `= z` everywhere
    theorem backwardDet_of_periodic, backwardDet_of_recurrence, blind_of_poly : three classes of such `ι`
    theorem invariant_blind, invariant_blind_poly, invariant_blind_periodic, invariant_blind_recurrence

Backward deterministic are: periodic sequences (values in a finite group of the evaluations of the boundary word
`t₀^{LM} t₃^{-f³M} t₋₃^{-f³M}`, counts modulo an integer), sequences with vanishing iterated difference (polynomial
in `M`: additive invariants of degree one, areas and tensor areas, evaluations in a nilpotent group) and sequences
with a linear recurrence that can be run backwards (matrix coefficients of the evaluations in a linear group).
So none of these can prove that the scales `2 ≤ M < f` have no tiling.  The lemmas are elementary; the content is
the theorem `betaTilable_ge` they are applied to.  A negative result on a class of methods; not prime-case work.
No sorry, no native_decide.
-/
import Erdos634.Draft.ResidueSeed

namespace Erdos634.Draft.Blind
open Erdos634.Draft.UniformThreshold (BetaTilable)
open Erdos634.Draft.Residue (betaTilable_ge)

/-- backward deterministic at the value `z`: if `ι` is `z` at all later arguments, it is `z` here -/
def BackwardDet {X : Type*} (ι : ℕ → X) (z : X) : Prop :=
  ∀ M, (∀ j, 1 ≤ j → ι (M + j) = z) → ι M = z

/-- a backward deterministic sequence that is `z` from `f` on is `z` everywhere -/
theorem blind_of_backward {X : Type*} (ι : ℕ → X) (z : X) (hb : BackwardDet ι z) (f : ℕ)
    (hf : ∀ M, f ≤ M → ι M = z) : ∀ M, ι M = z := by
  have key : ∀ k M, f ≤ M + k → ι M = z := by
    intro k
    induction k with
    | zero => intro M h; exact hf M (by omega)
    | succ k ih =>
      intro M h
      exact hb M (fun j hj => ih (M + j) (by omega))
  intro M
  exact key f M (by omega)

/-- periodic sequences are backward deterministic -/
theorem backwardDet_of_periodic {X : Type*} (ι : ℕ → X) (z : X) (P : ℕ) (hP : 1 ≤ P)
    (h : ∀ M, ι (M + P) = ι M) : BackwardDet ι z :=
  fun M hM => (h M).symm.trans (hM P hP)

/-- a linear recurrence that can be run backwards: `ι M` is a combination of the `d` following values -/
theorem backwardDet_of_recurrence {R A : Type*} [Semiring R] [AddCommMonoid A] [Module R A] (ι : ℕ → A) (d : ℕ)
    (c : ℕ → R) (h : ∀ M, ι M = ∑ j ∈ Finset.range d, c j • ι (M + 1 + j)) : BackwardDet ι 0 := by
  intro M hM
  rw [h M]
  refine Finset.sum_eq_zero (fun j _ => ?_)
  have h1 := hM (1 + j) (by omega)
  rw [← Nat.add_assoc] at h1
  rw [h1, smul_zero]

/-- the difference of a sequence -/
def diff {A : Type*} [AddCommGroup A] (ι : ℕ → A) : ℕ → A := fun M => ι (M + 1) - ι M

/-- a sequence with vanishing `k`-th difference (a polynomial of degree `< k`) that is zero from `f` on is zero -/
theorem blind_of_poly {A : Type*} [AddCommGroup A] :
    ∀ (k : ℕ) (ι : ℕ → A), (∀ M, (diff^[k] ι) M = 0) → ∀ f : ℕ, (∀ M, f ≤ M → ι M = 0) → ∀ M, ι M = 0 := by
  intro k
  induction k with
  | zero => intro ι h f _ M; exact h M
  | succ k ih =>
    intro ι h f hf
    have hd : ∀ M, diff ι M = 0 := by
      refine ih (diff ι) (fun M => ?_) f (fun M hM => ?_)
      · have := h M
        rwa [Function.iterate_succ_apply] at this
      · show ι (M + 1) - ι M = 0
        rw [hf M hM, hf (M + 1) (by omega), sub_zero]
    exact blind_of_backward ι 0 (backwardDet_of_periodic ι 0 1 le_rfl (fun M => sub_eq_zero.mp (hd M))) f hf

/-! ## On the base-β row -/

/-- **A backward deterministic invariant excludes no scale.**  For a member `(e, f)`: if `ι M = z` whenever the
scale `M` has a tiling, and `ι` is backward deterministic at `z`, then `ι M = z` at every scale. -/
theorem invariant_blind (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {X : Type*} (ι : ℕ → X)
    (z : X) (hinv : ∀ M, BetaTilable e f M → ι M = z) (hb : BackwardDet ι z) : ∀ M, ι M = z :=
  blind_of_backward ι z hb f (fun M hM => hinv M (betaTilable_ge e f he hef hco M hM))

/-- periodic invariants (values in a finite structure) -/
theorem invariant_blind_periodic (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {X : Type*}
    (ι : ℕ → X) (z : X) (hinv : ∀ M, BetaTilable e f M → ι M = z) (P : ℕ) (hP : 1 ≤ P)
    (h : ∀ M, ι (M + P) = ι M) : ∀ M, ι M = z :=
  invariant_blind e f he hef hco ι z hinv (backwardDet_of_periodic ι z P hP h)

/-- polynomial invariants (vanishing `k`-th difference) -/
theorem invariant_blind_poly (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {A : Type*}
    [AddCommGroup A] (ι : ℕ → A) (hinv : ∀ M, BetaTilable e f M → ι M = 0) (k : ℕ)
    (h : ∀ M, (diff^[k] ι) M = 0) : ∀ M, ι M = 0 :=
  blind_of_poly k ι h f (fun M hM => hinv M (betaTilable_ge e f he hef hco M hM))

/-- invariants with a linear recurrence that can be run backwards -/
theorem invariant_blind_recurrence (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) {R A : Type*}
    [Semiring R] [AddCommMonoid A] [Module R A] (ι : ℕ → A) (hinv : ∀ M, BetaTilable e f M → ι M = 0) (d : ℕ)
    (c : ℕ → R) (h : ∀ M, ι M = ∑ j ∈ Finset.range d, c j • ι (M + 1 + j)) : ∀ M, ι M = 0 :=
  invariant_blind e f he hef hco ι 0 hinv (backwardDet_of_recurrence ι d c h)

end Erdos634.Draft.Blind

#print axioms Erdos634.Draft.Blind.invariant_blind
#print axioms Erdos634.Draft.Blind.invariant_blind_poly
#print axioms Erdos634.Draft.Blind.invariant_blind_periodic
#print axioms Erdos634.Draft.Blind.invariant_blind_recurrence
