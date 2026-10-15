-- 30-60-90 tiles, n=6, a=(1,2,3). Generated file; the certificate is checked by the kernel.
-- Exact certificate over Q(sqrt3), checked by an independent Z[sqrt3] verifier
-- (congruence, containment, all-pairs disjointness, area; 4 T-junction incidences). Lattice (X,v) <-> (X, v*sqrt3), scale 4.
-- model vertices (30deg, 60deg, 90deg) = (pi/6, pi/3, pi/2); target angles (x pi/6) = [2, 2, 2].
import Erdos634.Draft.G3CCert
namespace Erdos634.Draft.G3RC1Tiling
open Erdos634.Draft.G3CCert

def cl0 : Bsp := Bsp.split (4,0) (2,2) (.split (2,0) (2,2) (.leaf ((0,0),(2,0),(2,2))) (.leaf ((2,0),(4,0),(2,2)))) (.split (4,0) (5,1) (.split (6,2) (2,2) (.split (5,1) (2,2) (.leaf ((2,2),(4,0),(5,1))) (.leaf ((2,2),(5,1),(6,2)))) (.split (4,2) (4,4) (.leaf ((4,4),(2,2),(4,2))) (.leaf ((4,4),(4,2),(6,2))))) (.split (6,0) (6,2) (.leaf ((4,0),(6,0),(6,2))) (.leaf ((6,0),(8,0),(6,2)))))

def cert : Cert := {
  target := ((0,0),(8,0),(4,4)),
  model := ((0,2),(-2,0),(0,0)),
  clusters := [cl0],
  seps := [] }

theorem cert_ok : cert.ok = true := by decide +kernel
theorem cert_len : cert.leaves.length = 8 := by decide +kernel

end Erdos634.Draft.G3RC1Tiling
