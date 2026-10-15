import Erdos634.LemmaPNode2
namespace Erdos634.Draft.LemmaPNode2Wrap
open Erdos634.LemmaPNode2
open Erdos634.Geometry Erdos634.CertCoord Erdos634.CertGeom Erdos634.ThickBlockingLemmas

theorem wrap_rr_bounds : 5 < rr ∧ rr < 6 :=
  rr_bounds

theorem wrap_node2_configuration_exists :
    w1t0.carrier ⊆ target63.carrier ∧ w1t1.carrier ⊆ target63.carrier ∧
    Disjoint (interior w1t0.carrier) (interior w1t1.carrier) :=
  node2_configuration_exists

theorem wrap_node2_jam {N : ℕ} (D : CongruentDissection N)
    (htarget : D.target.carrier = target63.carrier)
    (hmodel : D.model.Congruent w1t0)
    (i₀ i₁ : Fin N) (h₀ : D.tile i₀ = w1t0) (h₁ : D.tile i₁ = w1t1) : False :=
  node2_jam D htarget hmodel i₀ i₁ h₀ h₁

example : True := trivial
#print axioms wrap_node2_jam
end Erdos634.Draft.LemmaPNode2Wrap
