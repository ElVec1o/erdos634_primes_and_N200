import Erdos634.CornerParaLink

/-!
# CornerParaLink: wedge containment forces ray equality, wrapper
Key results: `endpoints_of_uIcc_abs_sub_eq`, `wedge_forces_ray_eq`.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.CornerParaLinkWrap
open Erdos634.Geometry Real InnerProductGeometry

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)] (o : Orientation ℝ V (Fin 2))

/-- Two reals in the unordered interval [0, σ] whose difference has absolute value |σ|
    must be the two endpoints. -/
theorem wrap_endpoints_of_uIcc_abs_sub_eq (σ s t : ℝ)
    (hs : s ∈ Set.uIcc 0 σ) (ht : t ∈ Set.uIcc 0 σ) (habs : |t - s| = |σ|) :
    (s = 0 ∧ t = σ) ∨ (s = σ ∧ t = 0) :=
  endpoints_of_uIcc_abs_sub_eq σ s t hs ht habs

/-- A sub-wedge of angle β inside a big wedge of the same angle β at the same vertex
    must have its boundary rays coincide with the big wedge's boundary rays. -/
theorem wrap_wedge_forces_ray_eq (u v u' v' : V) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu' : u' ≠ 0) (hv' : v' ≠ 0) (β : ℝ) (hβ0 : 0 < β) (hβπ : β < π)
    (hangle : InnerProductGeometry.angle u v = β)
    (hangle' : InnerProductGeometry.angle u' v' = β)
    (hmemu' : (o.oangle u u').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal)
    (hmemv' : (o.oangle u v').toReal ∈ Set.uIcc 0 (o.oangle u v).toReal) :
    (SameRay ℝ u u' ∧ SameRay ℝ v v') ∨ (SameRay ℝ v u' ∧ SameRay ℝ u v') :=
  wedge_forces_ray_eq o u v u' v' hu hv hu' hv' β hβ0 hβπ hangle hangle' hmemu' hmemv'

example : True := trivial

#print axioms wrap_endpoints_of_uIcc_abs_sub_eq
#print axioms wrap_wedge_forces_ray_eq

end Erdos634.Draft.CornerParaLinkWrap
