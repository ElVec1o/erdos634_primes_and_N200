import Erdos634.ChordChart

namespace Erdos634.Draft.ChordChartWrap

open Erdos634.ChordChart

theorem cc_abscissa_of_distances (a b c x y : ℝ)
    (h1 : x ^ 2 + y ^ 2 = b ^ 2) (h2 : (x - a) ^ 2 + y ^ 2 = c ^ 2) :
    2 * a * x = a ^ 2 + b ^ 2 - c ^ 2 :=
  abscissa_of_distances a b c x y h1 h2

theorem cc_reflected_numerator (e f : ℝ) :
    (e * f) ^ 2 + (f ^ 2 - e ^ 2) ^ 2 - (f ^ 2) ^ 2 = e ^ 2 * (e ^ 2 - f ^ 2) :=
  reflected_numerator e f

theorem cc_unreflected_numerator (e f : ℝ) :
    (e * f) ^ 2 + (f ^ 2) ^ 2 - (f ^ 2 - e ^ 2) ^ 2 = e ^ 2 * (3 * f ^ 2 - e ^ 2) :=
  unreflected_numerator e f

theorem cc_reflected_apex_left_of_mast (e f x y : ℝ) (he : 0 < e) (hef : e < f)
    (h1 : x ^ 2 + y ^ 2 = (f ^ 2 - e ^ 2) ^ 2) (h2 : (x - e * f) ^ 2 + y ^ 2 = (f ^ 2) ^ 2) :
    x < 0 :=
  reflected_apex_left_of_mast e f x y he hef h1 h2

example : cc_reflected_numerator 1 2 = reflected_numerator 1 2 := rfl

#print axioms cc_reflected_apex_left_of_mast

end Erdos634.Draft.ChordChartWrap
