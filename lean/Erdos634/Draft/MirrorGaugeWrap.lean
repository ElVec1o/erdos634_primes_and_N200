import Erdos634.MirrorGauge
namespace Erdos634.Draft.MirrorGaugeWrap
open Erdos634.MirrorGauge Erdos634.Geometry

theorem wrap_mirrorPt_injective : Function.Injective mirrorPt :=
  mirrorPt_injective

theorem wrap_mirrorPt_dist (p q : Plane) : dist (mirrorPt p) (mirrorPt q) = dist p q :=
  mirrorPt_dist p q

theorem wrap_Tri_det_mirror (T : Tri) : (Tri.mirror T).det = - T.det :=
  Tri.det_mirror T

theorem wrap_Tri_congruent_self_mirror (T : Tri) : T.Congruent (Tri.mirror T) :=
  Tri.congruent_self_mirror T

theorem wrap_mirror_flips_all_orientations {N : ℕ} (D : CongruentDissection N) (i : Fin N) :
    (CongruentDissection.mirror D).UnreflectedAt i ↔ (D.tile i).Reflected D.model :=
  mirror_flips_all_orientations D i

theorem wrap_no_global_orientation_count (N u r : ℕ) (hsum : u + r = N) (hodd : Odd N)
    (hzero : (u : ℤ) - r = 0) : False :=
  no_global_orientation_count N u r hsum hodd hzero

theorem wrap_wordMirror_involutive (n : ℕ) (w : ℕ → Bool) (j : ℕ) (hj : j ≤ n) :
    wordMirror n (wordMirror n w) j = w j :=
  wordMirror_involutive n w j hj

example : True := trivial
#print axioms wrap_mirror_flips_all_orientations
#print axioms wrap_no_global_orientation_count
end Erdos634.Draft.MirrorGaugeWrap
