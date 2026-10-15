import Erdos634.MarchKill
namespace Erdos634.Draft.MarchKillWrap
open Erdos634.MarchKill
open Erdos634.Geometry Erdos634.MarchCoords

theorem wrap_bg_gb_dies {N : ℕ} (D : Dissection N) {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂)
    {k₁ k₂ : Fin 3} (hshare : (D.tile i₁).pts k₁ = (D.tile i₂).pts k₂)
    (f h : ℝ) (hf : 1 < f) (hh : 0 < h)
    (hA0 : ((D.tile i₁).pts (k₁ + 1) - (D.tile i₁).pts k₁) 0 = -f)
    (hA1 : ((D.tile i₁).pts (k₁ + 1) - (D.tile i₁).pts k₁) 1 = 0)
    (hC0 : ((D.tile i₁).pts (k₁ + 2) - (D.tile i₁).pts k₁) 0 = dBG f - f)
    (hC1 : ((D.tile i₁).pts (k₁ + 2) - (D.tile i₁).pts k₁) 1 = h)
    (hD0 : ((D.tile i₂).pts (k₂ + 1) - (D.tile i₂).pts k₂) 0 = f)
    (hD1 : ((D.tile i₂).pts (k₂ + 1) - (D.tile i₂).pts k₂) 1 = 0)
    (hE0 : ((D.tile i₂).pts (k₂ + 2) - (D.tile i₂).pts k₂) 0 = dGB f)
    (hE1 : ((D.tile i₂).pts (k₂ + 2) - (D.tile i₂).pts k₂) 1 = h) :
    False :=
  bg_gb_dies D hne hshare f h hf hh hA0 hA1 hC0 hC1 hD0 hD1 hE0 hE1

example : True := trivial
#print axioms wrap_bg_gb_dies
end Erdos634.Draft.MarchKillWrap
