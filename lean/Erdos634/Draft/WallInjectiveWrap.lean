import Erdos634.WallInjective

namespace Erdos634.Draft.WallInjectiveWrap
open Erdos634.Geometry Erdos634.OrientBridge Erdos634.ChainInstance Erdos634.WallInjective

theorem wrap_shadows_disjoint {N : ℕ} (D : Dissection N) (g : Plane →ᵃ[ℝ] ℝ) (dir : Plane →ₗ[ℝ] ℝ)
    (c : ℝ) (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (i j : Fin N) (hij : i ≠ j) (m n : Fin 3)
    (hi1 : g ((D.tile i).pts m) = c) (hi2 : g ((D.tile i).pts (m + 1)) = c)
    (hi3 : g ((D.tile i).pts (m + 2)) < c)
    (hj1 : g ((D.tile j).pts n) = c) (hj2 : g ((D.tile j).pts (n + 1)) = c)
    (hj3 : g ((D.tile j).pts (n + 2)) < c) :
    edgeEnd D dir (i, m) ≤ edgePos D dir (j, n) ∨
      edgeEnd D dir (j, n) ≤ edgePos D dir (i, m) :=
  shadows_disjoint D g dir c hker i j hij m n hi1 hi2 hi3 hj1 hj2 hj3

example : True := trivial
#check @wrap_shadows_disjoint

end Erdos634.Draft.WallInjectiveWrap
