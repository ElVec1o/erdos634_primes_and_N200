import Erdos634.BridgeC

namespace Erdos634.Draft.BridgeCWrap

open Erdos634.BridgeC
open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.BaseChain
open Erdos634.Placement Erdos634.WallInjective Erdos634.Inflation Set

-- Re-exports: bridge (c) — base chain junctions as dissection theorems

theorem wrap_g_ends {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (p : Fin N × Fin 3) (hp : Erdos634.WallEdges.WallEdge D g c p) :
    g (edgeWest D dir p) = c ∧ g (edgeEast D dir p) = c :=
  g_ends D g c dir p hp

theorem wrap_junction_frontier_nonvertex {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ) (a b : Plane)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hvert : ∀ j : Fin 3, D.target.pts j = a ∨ D.target.pts j = b ∨ g (D.target.pts j) < c)
    {p : Plane} (hp : p ∈ D.target.carrier) (hgp : g p = c)
    (hstrict : min (dir a) (dir b) < dir p ∧ dir p < max (dir a) (dir b)) :
    p ∈ frontier D.target.carrier ∧ p ∉ Set.range D.target.pts :=
  junction_frontier_nonvertex D g c dir a b hbase hface hvert hp hgp hstrict

theorem wrap_avoid_alpha_of_multiset (x y α β γ : ℝ)
    (hmul : ({x, y, α} : Multiset ℝ) = {α, β, γ}) (hαβ : α ≠ β) (hαγ : α ≠ γ) :
    x ≠ α ∧ y ≠ α :=
  avoid_alpha_of_multiset x y α β γ hmul hαβ hαγ

theorem wrap_chain_edge_readings {N : ℕ} (D : Dissection N) (i : Fin N) (west east : Plane)
    (α β γ : ℝ) (hαβ : α ≠ β) (hαγ : α ≠ γ) (hbg : β ≠ γ)
    (hmul : ({(D.tile i).localAngle west, (D.tile i).localAngle east, α} : Multiset ℝ)
      = {α, β, γ})
    (hne : (D.tile i).localAngle west ≠ (D.tile i).localAngle east) :
    (Erdos634.OrientBridge.tileOrient D β i west = Orient.BG →
        (D.tile i).localAngle east = γ) ∧
      (Erdos634.OrientBridge.tileOrient D β i west = Orient.GB →
        (D.tile i).localAngle west = γ) :=
  chain_edge_readings D i west east α β γ hαβ hαγ hbg hmul hne

example : True := trivial

#print axioms Erdos634.BridgeC.g_ends
#print axioms Erdos634.BridgeC.avoid_alpha_of_multiset

end Erdos634.Draft.BridgeCWrap
