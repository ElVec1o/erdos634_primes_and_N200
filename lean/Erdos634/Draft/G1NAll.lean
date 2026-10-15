import Mathlib
import Erdos634.Draft.G1NInt
import Erdos634.Draft.G1NIso
import Erdos634.Draft.G1NF2
import Erdos634.Draft.G1NF34
import Erdos634.Draft.G1NFinal
import Erdos634.Draft.RSGWire

/-!
# Assembly of `integer_tile` for the shapes that are covered

`integer_tile_nonF1`: `D` any `CongruentDissection N` (any `N`, no primality, no residue condition), tile
`TwoPiThreeData alpha A B C` with `A B C` REAL and `IrrPi alpha`, target one of the isosceles shapes (`IsoTP`) or one of
`F2, F3, F3', F4, F4'` (`F2to4Shape`)  ==>  `(A,B,C) = K (a,b,c)`, `a b c` natural, `gcd(a,b) = 1`, `c^2 = a^2+ab+b^2`, `K > 0`.

NOT covered: the tile-similar target (the statement is FALSE there: ladder of an irrational tile),
the equilateral target, `F1`/`F1'` (the algebraic invariants do not force rationality there; only the primality-dependent geometric
argument is available).
-/

open scoped Classical

namespace Erdos634.Draft.G1NAll

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional

theorem integer_tile_F2to4 {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C) (hs : F2to4Shape D α) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  rcases hs with h | h | h | h | h
  · exact Erdos634.Draft.G1NF2.integer_tile_F2 D hα hm h
  · exact Erdos634.Draft.G1NF34.integer_tile_F3 D hα hm h
  · exact Erdos634.Draft.G1NF34.integer_tile_F3' D hα hm h
  · exact Erdos634.Draft.G1NF34.integer_tile_F4 D hα hm h
  · exact Erdos634.Draft.G1NF34.integer_tile_F4' D hα hm h

/-- **`integer_tile` (gap G1), for every target shape except tile-similar, equilateral, F1, F1'.** -/
theorem integer_tile_nonF1 {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C) (hs : IsoTP D α ∨ F2to4Shape D α) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ A = K * a ∧ B = K * b ∧ C = K * c := by
  rcases hs with h | h
  · exact Erdos634.Draft.G1NIso.integer_tile_iso D hα hm h
  · exact integer_tile_F2to4 D hα hm h

/-- Corollary: the hypothesis of `RSBArea.bridge`/`RSGWire.bridge_irr` is DERIVED for these shapes. -/
theorem bridge_derived {N : ℕ} (D : CongruentDissection N) {α A B C : ℝ} (hα : IrrPi α)
    (hm : D.model.TwoPiThreeData α A B C) (hs : IsoTP D α ∨ F2to4Shape D α) :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧
      c ^ 2 = a ^ 2 + a * b + b ^ 2 ∧ D.model.TwoPiThreeData α (K * a) (K * b) (K * c) ∧
      ∃ (s : Erdos634.Draft.FDDShapes.Shape) (σ : Equiv.Perm (Fin 3)) (k : ℕ), 0 < k ∧
        (∀ j, D.target.angleAt (σ j) = (s.triple j).1 * α + (s.triple j).2 * (Real.pi / 3)) ∧
        (∀ j, D.target.oppLen (σ j) = K * k * (s.sideV a b c j)) ∧ s.AreaEq a b k N := by
  obtain ⟨K, a, b, c, hK, ha, hb, hcop, hc, h1, h2, h3⟩ := integer_tile_nonF1 D hα hm hs
  have hm' : D.model.TwoPiThreeData α (K * a) (K * b) (K * c) := by
    rw [← h1, ← h2, ← h3]; exact hm
  exact ⟨K, a, b, c, hK, ha, hb, hcop, hc, hm', Erdos634.Draft.RSGWire.bridge_irr D hK a b c hcop hc hm'⟩

/-! ## Witness: the hypotheses of `integer_tile_nonF1` are satisfied by the REAL certified 2673-tile tiling
(isosceles target; re-described by `ISUReduce.iso_to_isoTP`).  The conclusion is then a real statement about a real tiling. -/

open Erdos634.Draft.G3CIsoControl in
theorem witness_iso_2673 :
    ∃ (α A B C : ℝ), IrrPi α ∧ D.model.TwoPiThreeData α A B C ∧ IsoTP D α := by
  obtain ⟨-, -, ⟨i, j, hij, h⟩, hne⟩ := Erdos634.Draft.ISUMain.control_hypotheses
  have hang : ∃ i j : Fin 3, i ≠ j ∧ D.target.angleAt i = D.target.angleAt j :=
    ⟨i, j, hij, Erdos634.Draft.ISUMain.angleAt_eq_of_oppLen_eq _ i j hij h⟩
  have hnE : ¬ Equilateral D := by
    intro hE
    exact hne (Erdos634.Draft.ISUMain.oppLen_eq_of_equilateral D hE)
  obtain ⟨α', a', b', c', hα', hm', hiso⟩ :=
    Erdos634.Draft.ISUReduce.iso_to_isoTP D α_irr data hang hnE
  exact ⟨α', a', b', c', hα', hm', hiso⟩

open Erdos634.Draft.G3CIsoControl in
theorem witness_conclusion_2673 :
    ∃ (K : ℝ) (a b c : ℕ), 0 < K ∧ 0 < a ∧ 0 < b ∧ Nat.Coprime a b ∧ c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨α, A, B, C, hα, hm, hiso⟩ := witness_iso_2673
  obtain ⟨K, a, b, c, hK, ha, hb, hcop, hc, -⟩ := integer_tile_nonF1 D hα hm (Or.inl hiso)
  exact ⟨K, a, b, c, hK, ha, hb, hcop, hc⟩

end Erdos634.Draft.G1NAll

#print axioms Erdos634.Draft.G1NAll.integer_tile_F2to4
#print axioms Erdos634.Draft.G1NAll.integer_tile_nonF1
#print axioms Erdos634.Draft.G1NAll.bridge_derived
#print axioms Erdos634.Draft.G1NAll.witness_iso_2673
#print axioms Erdos634.Draft.G1NAll.witness_conclusion_2673
