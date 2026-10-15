import Erdos634.MarchRunStep
namespace Erdos634.Draft.MarchRunStepWrap
open Erdos634.MarchRunStep
open Erdos634.Geometry Erdos634.MarchCoords

theorem wrap_circle_x (u0 u1 b c f : ℝ) (hf : 0 < f)
    (h1 : u0 ^ 2 + u1 ^ 2 = c ^ 2) (h2 : (u0 - f) ^ 2 + u1 ^ 2 = b ^ 2) :
    u0 = (c ^ 2 - b ^ 2 + f ^ 2) / (2 * f) :=
  circle_x u0 u1 b c f hf h1 h2

theorem wrap_bg_abscissa (u0 u1 f : ℝ) (hf : 1 < f)
    (h1 : u0 ^ 2 + u1 ^ 2 = (f ^ 2) ^ 2)
    (h2 : (u0 - f) ^ 2 + u1 ^ 2 = (f ^ 2 - 1) ^ 2) :
    u0 = dBG f :=
  bg_abscissa u0 u1 f hf h1 h2

theorem wrap_gb_abscissa (v0 v1 f : ℝ) (hf : 1 < f)
    (h1 : v0 ^ 2 + v1 ^ 2 = (f ^ 2 - 1) ^ 2)
    (h2 : (v0 - f) ^ 2 + v1 ^ 2 = (f ^ 2) ^ 2) :
    v0 = dGB f :=
  gb_abscissa v0 v1 f hf h1 h2

theorem wrap_heights_agree (u0 u1 v0 v1 f : ℝ) (hf : 1 < f)
    (hu : u0 ^ 2 + u1 ^ 2 = (f ^ 2) ^ 2) (hu0 : u0 = dBG f)
    (hv : v0 ^ 2 + v1 ^ 2 = (f ^ 2 - 1) ^ 2) (hv0 : v0 = dGB f)
    (hup : 0 < u1) (hvp : 0 < v1) : u1 = v1 :=
  heights_agree u0 u1 v0 v1 f hf hu hu0 hv hv0 hup hvp

theorem wrap_dist_sq_plane (x y : Plane) :
    dist x y ^ 2 = (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 :=
  dist_sq_plane x y

theorem wrap_run_step_bg_gb_dies {N : ℕ} (D : Dissection N) {i₁ i₂ : Fin N} (hne : i₁ ≠ i₂)
    {k₁ k₂ : Fin 3} (f : ℝ) (hf : 1 < f)
    (A B Dd X₁ X₂ : Plane)
    (hp₁ : (D.tile i₁).pts k₁ = B) (hp₁A : (D.tile i₁).pts (k₁ + 1) = A)
    (hp₁X : (D.tile i₁).pts (k₁ + 2) = X₁)
    (hp₂ : (D.tile i₂).pts k₂ = B) (hp₂D : (D.tile i₂).pts (k₂ + 1) = Dd)
    (hp₂X : (D.tile i₂).pts (k₂ + 2) = X₂)
    (hAB0 : B 0 - A 0 = f) (hAB1 : B 1 - A 1 = 0)
    (hBD0 : Dd 0 - B 0 = f) (hBD1 : Dd 1 - B 1 = 0)
    (hX1A : (X₁ 0 - A 0) ^ 2 + (X₁ 1 - A 1) ^ 2 = (f ^ 2) ^ 2)
    (hX1B : (X₁ 0 - B 0) ^ 2 + (X₁ 1 - B 1) ^ 2 = (f ^ 2 - 1) ^ 2)
    (hX2B : (X₂ 0 - B 0) ^ 2 + (X₂ 1 - B 1) ^ 2 = (f ^ 2 - 1) ^ 2)
    (hX2D : (X₂ 0 - Dd 0) ^ 2 + (X₂ 1 - Dd 1) ^ 2 = (f ^ 2) ^ 2)
    (hup1 : 0 < X₁ 1 - B 1) (hup2 : 0 < X₂ 1 - B 1) :
    False :=
  run_step_bg_gb_dies D hne f hf A B Dd X₁ X₂ hp₁ hp₁A hp₁X hp₂ hp₂D hp₂X
    hAB0 hAB1 hBD0 hBD1 hX1A hX1B hX2B hX2D hup1 hup2

theorem wrap_run_step_bg_gb_dies_of_dist {N : ℕ} (D : Dissection N) {i₁ i₂ : Fin N}
    (hne : i₁ ≠ i₂) {k₁ k₂ : Fin 3} (f : ℝ) (hf : 1 < f)
    (A B Dd X₁ X₂ : Plane)
    (hp₁ : (D.tile i₁).pts k₁ = B) (hp₁A : (D.tile i₁).pts (k₁ + 1) = A)
    (hp₁X : (D.tile i₁).pts (k₁ + 2) = X₁)
    (hp₂ : (D.tile i₂).pts k₂ = B) (hp₂D : (D.tile i₂).pts (k₂ + 1) = Dd)
    (hp₂X : (D.tile i₂).pts (k₂ + 2) = X₂)
    (hAB0 : B 0 - A 0 = f) (hAB1 : B 1 - A 1 = 0)
    (hBD0 : Dd 0 - B 0 = f) (hBD1 : Dd 1 - B 1 = 0)
    (hd1A : dist X₁ A = f ^ 2) (hd1B : dist X₁ B = f ^ 2 - 1)
    (hd2B : dist X₂ B = f ^ 2 - 1) (hd2D : dist X₂ Dd = f ^ 2)
    (hup1 : 0 < X₁ 1 - B 1) (hup2 : 0 < X₂ 1 - B 1) :
    False :=
  run_step_bg_gb_dies_of_dist D hne f hf A B Dd X₁ X₂ hp₁ hp₁A hp₁X hp₂ hp₂D hp₂X
    hAB0 hAB1 hBD0 hBD1 hd1A hd1B hd2B hd2D hup1 hup2

example : True := trivial
#print axioms wrap_run_step_bg_gb_dies
#print axioms wrap_run_step_bg_gb_dies_of_dist
end Erdos634.Draft.MarchRunStepWrap
