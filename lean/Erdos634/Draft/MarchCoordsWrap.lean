import Erdos634.MarchCoords
namespace Erdos634.Draft.MarchCoordsWrap
open Erdos634.MarchCoords

theorem wrap_gb_left (f : ℝ) (hf : f ≠ 0) : dGB f ^ 2 + h2 f = (f ^ 2 - 1) ^ 2 :=
  gb_left f hf

theorem wrap_gb_right (f : ℝ) (hf : f ≠ 0) : (dGB f - f) ^ 2 + h2 f = (f ^ 2) ^ 2 :=
  gb_right f hf

theorem wrap_bg_left (f : ℝ) (hf : f ≠ 0) : dBG f ^ 2 + h2 f = (f ^ 2) ^ 2 :=
  bg_left f hf

theorem wrap_bg_right (f : ℝ) (hf : f ≠ 0) : (dBG f - f) ^ 2 + h2 f = (f ^ 2 - 1) ^ 2 :=
  bg_right f hf

theorem wrap_offsets_complementary (f : ℝ) (hf : f ≠ 0) : dGB f + dBG f = f :=
  offsets_complementary f hf

theorem wrap_derived_run_shift (f : ℝ) (hf : f ≠ 0) : dBG f - dGB f = 2 * f - 1 / f :=
  derived_run_shift f hf

example : True := trivial
#print axioms wrap_gb_left
#print axioms wrap_offsets_complementary
end Erdos634.Draft.MarchCoordsWrap
