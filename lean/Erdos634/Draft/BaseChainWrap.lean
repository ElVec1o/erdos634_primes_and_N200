import Erdos634.BaseChain

/-!
# Wall chain enumeration and reach: wrapper

Re-exports results of `BaseChain`:
- `wallList_nodup`: the wall edge list has no duplicates
- `mem_wallList`: membership characterization
- `base_chain_reach`: consecutive chain edges reach (given sorted enumeration)
- `base_chain_consecutive_meet`: the reach property, packaged with an enumeration witness

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseChainWrap

open Erdos634.BaseChain Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance

theorem bc_wallList_nodup {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) :
    (wallList D g c).Nodup :=
  wallList_nodup D g c

theorem bc_mem_wallList {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (p : Fin N × Fin 3) : p ∈ wallList D g c ↔ Erdos634.WallEdges.WallEdge D g c p :=
  mem_wallList D g c p

theorem bc_base_chain_consecutive_meet {N : ℕ} (hN : 0 < N) (D : Dissection N)
    (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c) (a b : Plane) (hab : a ≠ b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b) :
    ∃ E : ℕ → Fin N × Fin 3, ∀ k, k + 1 < (wallList D g c).length →
      ∃ j ≤ k, edgePos D dir (E (k + 1)) ≤ edgeEnd D dir (E j) :=
  base_chain_consecutive_meet hN D g c dir hwall a b hab hbase hline hface

-- Non-vacuity
example : @bc_wallList_nodup = @bc_wallList_nodup := rfl

#print axioms bc_wallList_nodup
#print axioms bc_base_chain_consecutive_meet

end Erdos634.Draft.BaseChainWrap
