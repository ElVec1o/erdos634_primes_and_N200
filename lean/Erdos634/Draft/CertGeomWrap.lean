import Erdos634.CertGeom

namespace Erdos634.Draft.CertGeomWrap

open Erdos634.CertGeom Erdos634.Geometry

theorem cg_carrier_subset_of_pts_mem {t T : Tri} (h : ∀ k, t.pts k ∈ T.carrier) :
    t.carrier ⊆ T.carrier :=
  carrier_subset_of_pts_mem h

theorem cg_le_of_forall_pts_le {t : Tri} (f : Plane →ᵃ[ℝ] ℝ) {c : ℝ} (h : ∀ k, f (t.pts k) ≤ c) :
    ∀ x ∈ t.carrier, f x ≤ c :=
  le_of_forall_pts_le f h

theorem cg_mem_carrier_of_combo (T : Tri) (x : Plane) (w : Fin 3 → ℝ)
    (hsum : w 0 + w 1 + w 2 = 1) (hnn : ∀ k, 0 ≤ w k)
    (hx : x = w 0 • T.pts 0 + w 1 • T.pts 1 + w 2 • T.pts 2) :
    x ∈ T.carrier :=
  mem_carrier_of_combo T x w hsum hnn hx

theorem cg_interiors_disjoint_of_separating {t u : Tri} (f : Plane →ᵃ[ℝ] ℝ) (hf : f.linear ≠ 0)
    (c : ℝ) (h1 : ∀ x ∈ t.carrier, f x ≤ c) (h2 : ∀ x ∈ u.carrier, c ≤ f x) :
    Disjoint (interior t.carrier) (interior u.carrier) :=
  interiors_disjoint_of_separating f hf c h1 h2

example : True := trivial

#print axioms cg_interiors_disjoint_of_separating

end Erdos634.Draft.CertGeomWrap
