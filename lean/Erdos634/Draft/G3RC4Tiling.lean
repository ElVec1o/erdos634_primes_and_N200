-- 30-60-90 tiles, n=6, a=(1,2,3). Generated file; the certificate is checked by the kernel.
-- Exact certificate over Q(sqrt3), checked by an independent Z[sqrt3] verifier
-- (congruence, containment, all-pairs disjointness, area; 5 T-junction incidences). Lattice (X,v) <-> (X, v*sqrt3), scale 4.
-- model vertices (30deg, 60deg, 90deg) = (pi/6, pi/3, pi/2); target angles (x pi/6) = [3, 1, 2].
import Erdos634.Draft.G3CCert
namespace Erdos634.Draft.G3RC4Tiling
open Erdos634.Draft.G3CCert

def cl0 : Bsp := Bsp.split (2,2) (0,4) (.split (0,2) (2,2) (.leaf ((0,4),(0,2),(2,2))) (.split (2,0) (0,2) (.leaf ((0,2),(0,0),(2,0))) (.split (2,2) (2,0) (.leaf ((2,2),(2,0),(4,0))) (.leaf ((0,2),(2,0),(2,2)))))) (.split (4,0) (6,2) (.split (6,2) (2,2) (.split (6,2) (3,1) (.leaf ((6,2),(3,1),(4,0))) (.leaf ((6,2),(2,2),(3,1)))) (.split (3,3) (2,2) (.leaf ((2,2),(6,2),(3,3))) (.leaf ((2,2),(3,3),(0,4))))) (.split (9,1) (8,0) (.leaf ((12,0),(9,1),(8,0))) (.split (8,0) (5,1) (.leaf ((8,0),(5,1),(4,0))) (.split (5,1) (9,1) (.leaf ((9,1),(6,2),(5,1))) (.leaf ((8,0),(9,1),(5,1)))))))

def cert : Cert := {
  target := ((0,0),(12,0),(0,4)),
  model := ((0,2),(-2,0),(0,0)),
  clusters := [cl0],
  seps := [] }

theorem cert_ok : cert.ok = true := by decide +kernel
theorem cert_len : cert.leaves.length = 12 := by decide +kernel

end Erdos634.Draft.G3RC4Tiling
