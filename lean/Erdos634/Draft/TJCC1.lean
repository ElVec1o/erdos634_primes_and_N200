-- No sorry, no native_decide.
-- The 8-tile 30-60-90 tiling C1 (equilateral target by 30-60-90 tiles, reflections, T-junctions:
-- (5,1) is a vertex of tiles 2,3 and an interior point of tile 6's edge (6,2)-(4,0)); lattice (u,v) <-> (u, v*sqrt 3).
-- Setup and helpers.  Applications of the five pointwise lemmas are in TJCC1App.lean.
import Erdos634.Draft.G3RC1Tiling
import Erdos634.Draft.G3RCCommon
import Erdos634.Draft.TJCHelp

namespace Erdos634.Draft.TJCC1

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.TJCHelp Erdos634.Draft.G3CCert
  Erdos634.Draft.G3RCCommon Erdos634.Draft.G3RC1Tiling

/-- the real dissection (bare `Dissection`; the five lemmas need no congruence) -/
noncomputable abbrev D : Dissection cert.leaves.length := (cd cert cert_ok).toDissection

abbrev tl (n : ℕ) (h : n < 8 := by decide) : Fin cert.leaves.length :=
  ⟨n, by rw [cert_len]; exact h⟩

theorem tile_pts_gen (i : Fin cert.leaves.length) (k : Fin 3) :
    (D.tile i).pts k = toPt (vtx (cert.leaves.get i) k) := by
  show ((cd cert cert_ok).tile i).pts k = _
  rw [tile_eq]; exact triOf_pts _ _ k

theorem tile_eq' (i : Fin cert.leaves.length) :
    D.tile i = triOf (cert.leaves.get i) (pos_of_mem cert_ok (List.get_mem _ _)) := tile_eq cert cert_ok i

theorem leftDir_triOf (t : LT) (h : 0 < cross t.1 t.2.1 t.2.2) (k : Fin 3) :
    (triOf t h).leftDir k = toPt (vtx t (k + 1)) - toPt (vtx t k) := by
  have hd : 0 < (triOf t h).det := by
    unfold triOf; rw [det_mkTri]; exact det3_pos h
  unfold Tri.leftDir
  rw [if_pos hd, triOf_pts, triOf_pts]

theorem D_leftDir (i : Fin cert.leaves.length) (k : Fin 3) :
    (D.tile i).leftDir k = toPt (vtx (cert.leaves.get i) (k + 1)) - toPt (vtx (cert.leaves.get i) k) := by
  rw [tile_eq']; exact leftDir_triOf _ _ k

theorem toPt_eq (a b : ℤ) : toPt (a, b) = mkPt (a : ℝ) ((b : ℝ) * Real.sqrt 3) := rfl

theorem pt_of (i : Fin cert.leaves.length) (k : Fin 3) (a b : ℤ) (hv : vtx (cert.leaves.get i) k = (a, b)) :
    (D.tile i).pts k = mkPt (a : ℝ) ((b : ℝ) * Real.sqrt 3) := by
  rw [tile_pts_gen, hv]; rfl

theorem lin_toPt (a b : ℝ) (p : LP) : lin a b (toPt p) = a * (p.1 : ℝ) + b * ((p.2 : ℝ) * Real.sqrt 3) := by
  show lin a b (mkPt _ _) = _
  rw [lin_mkPt]; rfl

theorem s3pos' : (0 : ℝ) < Real.sqrt 3 := s3pos

end Erdos634.Draft.TJCC1
