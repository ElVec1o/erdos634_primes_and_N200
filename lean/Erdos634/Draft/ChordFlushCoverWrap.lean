import Erdos634.ChordFlushCover

namespace Erdos634.Draft.ChordFlushCoverWrap
open Erdos634.Geometry Erdos634.ChordTraceReal

theorem wrap_eq_of_combo_eq_lb {a b c s : ℝ} (ha : c ≤ a) (hb : c ≤ b)
    (hs0 : 0 < s) (hs1 : s < 1) (heq : s * a + (1 - s) * b = c) : a = c ∧ b = c :=
  eq_of_combo_eq_lb ha hb hs0 hs1 heq

theorem wrap_upperFlush_edge_endpoints_eq_c (T : Tri) (f : Plane →ₗ[ℝ] ℝ) (c : ℝ)
    (hup : ∀ y ∈ T.carrier, c ≤ f y) {k : Fin 3} {x : Plane}
    (hx : x ∈ T.edge k) (hxv : ∀ m, x ≠ T.pts m) (hfx : f x = c) :
    f (T.pts k) = c ∧ f (T.pts (k + 1)) = c :=
  upperFlush_edge_endpoints_eq_c T f c hup hx hxv hfx

example : True := trivial
#print axioms wrap_upperFlush_edge_endpoints_eq_c

end Erdos634.Draft.ChordFlushCoverWrap
