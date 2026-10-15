import Erdos634.CertNode

namespace Erdos634.Draft.CertNodeWrap

open Erdos634.CertNode Erdos634.Geometry

theorem cn_sr_pos {Dn : ℝ} (hD : 0 < Dn) : 0 < sr Dn := sr_pos hD

theorem cn_sr_sq {Dn : ℝ} (hD : 0 < Dn) : sr Dn ^ 2 = Dn := sr_sq hD

theorem cn_sr_lt {Dn B : ℝ} (hD : 0 < Dn) (hB : 0 < B) (h : Dn < B ^ 2) : sr Dn < B :=
  sr_lt hD hB h

theorem cn_rp_zero (Dn x y : ℝ) : rp Dn x y 0 = x := rp_zero Dn x y

theorem cn_rp_one (Dn x y : ℝ) : rp Dn x y 1 = y * sr Dn := rp_one Dn x y

theorem cn_exists_rp {Dn : ℝ} (hD : 0 < Dn) (p : Plane) : ∃ X Y : ℝ, p = rp Dn X Y :=
  exists_rp hD p

example : cn_sr_sq (show (0:ℝ) < 4 by norm_num) = sr_sq (show (0:ℝ) < 4 by norm_num) := rfl

#print axioms cn_exists_rp

end Erdos634.Draft.CertNodeWrap
