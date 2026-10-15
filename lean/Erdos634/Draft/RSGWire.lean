import Mathlib
import Erdos634.Draft.RSBArea
import Erdos634.Draft.RSBReduce
import Erdos634.Draft.RSBWitness
import Erdos634.Draft.ADMCore
import Erdos634.Draft.FluxCRow5TwoPiThreeFull

/-!
# RSG: wiring of the irrationality of `α/π` (derived) and of the equilateral prime case into the RSB bridge.
The integer-tile normalization remains a hypothesis.
-/

open scoped Classical

namespace Erdos634.Draft.RSGWire

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.FDDShapes
  Erdos634.Draft.RSBSine Erdos634.Draft.RSBCorner Erdos634.Draft.RSBArea Erdos634.Draft.RSBReduce

variable {N : ℕ}

/-- G3: `IrrPi α` from the integer 120-degree triple (Niven), via `ADMCore.irrPi_of_triple`. -/
theorem irrPi_of_model (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) : IrrPi α := by
  obtain ⟨hcosK, hcK, haK, hbK⟩ := cos_alpha_of_TwoPiThree D.model hm
  have ha : 0 < a := by
    have : (0 : ℝ) < a := (pos_iff_pos_of_mul_pos haK).mp hK
    exact_mod_cast this
  have hb : 0 < b := by
    have : (0 : ℝ) < b := (pos_iff_pos_of_mul_pos hbK).mp hK
    exact_mod_cast this
  have hc0 : 0 < c := by
    have : (0 : ℝ) < c := (pos_iff_pos_of_mul_pos hcK).mp hK
    exact_mod_cast this
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc0.ne'
  refine Erdos634.Draft.ADMCore.irrPi_of_triple a b c ha hb hc0 hc α ?_
  rw [hcosK]; field_simp

theorem bridge_irr (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) :
    ∃ (s : Shape) (σ : Equiv.Perm (Fin 3)) (k : ℕ), 0 < k ∧
      (∀ j, D.target.angleAt (σ j) = (s.triple j).1 * α + (s.triple j).2 * (Real.pi / 3)) ∧
      (∀ j, D.target.oppLen (σ j) = K * k * (s.sideV a b c j)) ∧
      s.AreaEq a b k N :=
  bridge D hK a b c hcop hc (irrPi_of_model D hK a b c hc hm) hm

theorem reduction_tiling_irr (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) (hN : N.Prime) :
    (∀ i, D.target.angleAt i = Real.pi / 3) ∨
    ((∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) ∧
      ¬ (∀ i, D.target.angleAt i = Real.pi / 3)) :=
  reduction_tiling D hK a b c ha hb hcop hc (irrPi_of_model D hK a b c hc hm) hm hN

/-- G2 wired: prime `N > 3`: the equilateral disjunct is discharged by `Row5.theoremE_twoPiThree_full`. -/
theorem reduction_tiling_noEq (D : CongruentDissection N) {α K : ℝ} (hK : 0 < K) (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hcop : Nat.Coprime a b) (hc : c ^ 2 = a ^ 2 + a * b + b ^ 2)
    (hm : D.model.TwoPiThreeData α (K * a) (K * b) (K * c)) (hN : N.Prime) (h3 : 3 < N) :
    (∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j) ∧
      ¬ (∀ i, D.target.angleAt i = Real.pi / 3) := by
  rcases reduction_tiling_irr D hK a b c ha hb hcop hc hm hN with h | h
  · exact absurd ⟨hN, h3⟩
      (Erdos634.Geometry.Row5TwoPiThreeFull.Row5.theoremE_twoPiThree_full D
        (irrPi_of_model D hK a b c hc hm) hm h)
  · exact h

/-! ### Without primality the conclusion fails on the real `N = 4` tiling `D357`
(target homothetic to the scalene `(3,5,7)` tile: no two equal angles). -/

open Erdos634.Draft.FluxPaperWitness in
theorem control_noPrime :
    ¬ ((∃ i j : Fin 3, i ≠ j ∧ D357.target.angleAt i = D357.target.angleAt j) ∧
      ¬ (∀ i, D357.target.angleAt i = Real.pi / 3)) := by
  rintro ⟨⟨i, j, hij, heq⟩, -⟩
  obtain ⟨s, σ, k, hs, -, hang, -⟩ := Erdos634.Draft.RSBWitness.w357
  subst hs
  obtain ⟨x, rfl⟩ := σ.surjective i
  obtain ⟨y, rfl⟩ := σ.surjective j
  have hxy : x ≠ y := fun h => hij (by rw [h])
  rw [hang x, hang y] at heq
  have hirr := α357_irr
  have t : ∀ j, Shape.tileSimilar.triple j = ![(1, 0), (-1, 1), (0, 2)] j := fun j => rfl
  rw [t x, t y] at heq
  fin_cases x <;> fin_cases y <;> simp at hxy heq <;>
    first
    | (exact hirr ⟨1 / 6, by push_cast; linarith⟩)
    | (exact hirr ⟨1 / 6, by push_cast; linarith⟩)
    | (exact hirr ⟨2 / 3, by push_cast; linarith⟩)
    | (exact hirr ⟨-1 / 3, by push_cast; linarith⟩)

#print axioms Erdos634.Draft.RSGWire.irrPi_of_model
#print axioms Erdos634.Draft.RSGWire.bridge_irr
#print axioms Erdos634.Draft.RSGWire.reduction_tiling_irr
#print axioms Erdos634.Draft.RSGWire.reduction_tiling_noEq
#print axioms Erdos634.Draft.RSGWire.control_noPrime

end Erdos634.Draft.RSGWire
