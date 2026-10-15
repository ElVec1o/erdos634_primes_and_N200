import Erdos634.GaloisMirror

namespace Erdos634.Draft.GaloisMirrorWrap

open Erdos634.GaloisMirror Erdos634.Geometry Erdos634.BaseBetaQuad Erdos634.MirrorGauge

/-- Thin wrapper: the coordinate embedding intertwines `qconj` with the plane mirror. -/
theorem wrap_pt_qconj (e f : ℚ) (z : ℚ × ℚ) :
    pt e f (qconj z) = mirrorPt (pt e f z) :=
  pt_qconj e f z

/-- Thin wrapper: the Galois conjugate of a tile is its mirror. -/
theorem wrap_Tri_mirror_of_coords (e f : ℚ) (T : Tri) (z : Fin 3 → ℚ × ℚ)
    (h : ∀ k, T.pts k = pt e f (z k)) (k : Fin 3) :
    (MirrorGauge.Tri.mirror T).pts k = pt e f (qconj (z k)) :=
  Tri.mirror_of_coords e f T z h k

/-- Thin wrapper: Galois-stable ↔ mirror-invariant on the coordinate plane. -/
theorem wrap_galoisStable_iff_mirrorInvariant (e f : ℚ) (Q : Plane → Prop) :
    GaloisStable e f Q ↔ ∀ z : ℚ × ℚ, Q (pt e f z) ↔ Q (mirrorPt (pt e f z)) :=
  galoisStable_iff_mirrorInvariant e f Q

/-- Thin wrapper: the norm form is Galois-stable. -/
theorem wrap_norm_qconj (e f : ℚ) (z : ℚ × ℚ) :
    qmul e f (qconj z) (qconj (qconj z)) = qmul e f z (qconj z) :=
  norm_qconj e f z

-- Non-vacuity: σ genuinely moves the point (0,1) at (e,f)=(1,2).
example : pt 1 2 (qconj (0, 1)) ≠ pt 1 2 (0, 1) := sigma_moves_a_point

#print axioms wrap_pt_qconj
#print axioms wrap_galoisStable_iff_mirrorInvariant

end Erdos634.Draft.GaloisMirrorWrap
