import Erdos634.ChordFinsetGeometricChainBase
namespace Erdos634.Draft.ChordFinsetGeometricChainBaseWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_not_interior_of_all_excluded {N : ℕ} (D : Erdos634.Geometry.Dissection N)
    (f : Plane →ₗ[ℝ] ℝ) (hf : f ≠ 0) (c : ℝ) {P bound : Plane}
    (R S : Fin N → Plane)
    (hglobal : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (R k) (S k) ∧ R k ≠ S k ∧
        (D.tile k).carrier ∩ {x | f x = c} = segment ℝ (R k) (S k))
    (hexcl : ∀ k : Fin N, (∃ a, f ((D.tile k).pts a) < c) → (∃ b, c < f ((D.tile k).pts b)) →
      Wbtw ℝ P (S k) bound)
    (hboundfc : f bound = c) :
    ∀ k : Fin N, bound ∉ interior (D.tile k).carrier :=
  not_interior_of_all_excluded D f hf c R S hglobal hexcl hboundfc

example : True := trivial
#print axioms not_interior_of_all_excluded
end Erdos634.Draft.ChordFinsetGeometricChainBaseWrap
