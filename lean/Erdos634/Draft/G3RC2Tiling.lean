-- 30-60-90 tiles, n=6, a=(1,2,3). Generated file; the certificate is checked by the kernel.
-- Exact certificate over Q(sqrt3), checked by an independent Z[sqrt3] verifier
-- (congruence, containment, all-pairs disjointness, area; 2 T-junction incidences). Lattice (X,v) <-> (X, v*sqrt3), scale 4.
-- model vertices (30deg, 60deg, 90deg) = (pi/6, pi/3, pi/2); target angles (x pi/6) = [1, 1, 4].
import Erdos634.Draft.G3CCert
namespace Erdos634.Draft.G3RC2Tiling
open Erdos634.Draft.G3CCert

def cl0 : Bsp := Bsp.split (4,0) (6,2) (.split (3,1) (4,0) (.leaf ((4,0),(6,2),(3,1))) (.leaf ((4,0),(3,1),(0,0)))) (.split (6,2) (8,0) (.split (8,0) (9,1) (.leaf ((8,0),(9,1),(6,2))) (.leaf ((8,0),(12,0),(9,1)))) (.split (4,0) (7,1) (.leaf ((4,0),(7,1),(6,2))) (.leaf ((4,0),(8,0),(7,1)))))

def cert : Cert := {
  target := ((0,0),(12,0),(6,2)),
  model := ((0,2),(-2,0),(0,0)),
  clusters := [cl0],
  seps := [] }

theorem cert_ok : cert.ok = true := by decide +kernel
theorem cert_len : cert.leaves.length = 6 := by decide +kernel

end Erdos634.Draft.G3RC2Tiling
