import Erdos634.WallEndpoints

namespace Erdos634.Draft.WallEndpointsWrap
open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.BaseChain
open Erdos634.Placement Erdos634.WallInjective Erdos634.WallEndpoints

theorem wrap_chain_endpoints {N : ℕ} (hN : 0 < N) (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ wallList D g c, g ((D.tile p.1).pts (p.2 + 2)) < c) :
    ∃ E : ℕ → Fin N × Fin 3, ∃ n : ℕ, n = (wallList D g c).length ∧ 0 < n ∧
      edgeWest D dir (E 0) = a ∧ edgeEast D dir (E (n - 1)) = b ∧
      (∀ m, m + 1 < n → edgeEast D dir (E m) = edgeWest D dir (E (m + 1))) ∧
      (∀ m, m < n → E m ∈ wallList D g c) ∧
      (∀ m1 m2, m1 < n → m2 < n → E m1 = E m2 → m1 = m2) ∧
      (∀ m, 0 < m → m < n → dir a < edgePos D dir (E m)) ∧
      (∀ m, m + 1 < n → edgeEnd D dir (E m) < dir b) ∧
      (∀ m, m < n → edgePos D dir (E m) < edgeEnd D dir (E m)) ∧
      (∀ x ∈ wallList D g c, ∃ i < n, E i = x) :=
  chain_endpoints hN D g c dir hker hwall a b hab hdirab hbase hline hface hthird

example : True := trivial
#print axioms wrap_chain_endpoints

end Erdos634.Draft.WallEndpointsWrap
