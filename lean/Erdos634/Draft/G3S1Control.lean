-- Counterexample check for the S1 leaf of chain_gen3. No sorry, no native_decide.
-- S1Closed N := forall D α β a b c r, IrrPi α -> 3α+2β=π -> ThreeAlphaData -> a=rc -> b=(1-r²)c -> TgtAngles D β β (3α) -> False.
-- At N=44 the real dissection (Tiling44Bridge.dissection) satisfies every premise, so S1Closed 44 is FALSE.
import Erdos634.Draft.G3CLeafFalse
import Erdos634.Draft.CompositeS1Arith

open scoped Classical

namespace Erdos634.Draft.G3S1Control

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeS1Arith

theorem not_s1Closed_44 : ¬ S1Closed 44 := by
  intro g
  have h : Tiling44.tiles.length = 44 := by decide
  rw [← h] at g
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := scaleBaseBeta_premises_44
  exact g D44 _ _ 16 24 32 (1 / 2) h1 h2 h3 h4 h5 h6

/-- The arithmetic core fails at 44: (p,q,M) = (1,2,6): 44·9 = 36·11. -/
theorem not_s1Arith_44 : ¬ S1Arith 44 := fun h =>
  h 1 2 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Consistency: the arithmetic core is TRUE at 22 (leaf non-hollow). -/
theorem s1Arith_22' : S1Arith 22 := s1Arith_22

end Erdos634.Draft.G3S1Control

#print axioms Erdos634.Draft.G3S1Control.not_s1Closed_44
#print axioms Erdos634.Draft.G3S1Control.not_s1Arith_44
