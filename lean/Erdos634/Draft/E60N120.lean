/-
Draft/E60N120.lean -- `GapE60 120`: no tile with an angle `π/3` (and an irrational angle) cuts an equilateral triangle
into 120 congruent triangles.

The pair table `E60Irr.Pairs60ChkSq 120 [(36, 10)]` (kernel check) leaves one pair that is rational and of the right
parity, `(36, 10)`: the tile `(8, 13, 15)` (angle `π/3` between the sides 8 and 15) on the equilateral triangle of
side `120`; at the scale 2 it is refuted by the `CheckM` certificate `Refl.MP120x36` (65,710 nodes).  The other pair
of the right parity, `(60, 6)`, has the non-square discriminant `2436` and is excluded by
`E60Irr.e60Pair_of_not_isSquare`.

Composite-N leaf; not prime-case work (used by `Draft/N120.lean`, with the commensurable-angle leaf `GAU.gapA_120` and
the certificate of the `F₁` pair `(6, 20)`).  No sorry, no native_decide.
-/
import Erdos634.Draft.E60Irr
import Erdos634.Refl.MP120x36Sound

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.E60N120

open Erdos634.Geometry Erdos634.Draft.TheoremPConditional Erdos634.Draft.Chain15 Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.E60Cert Erdos634.Draft.E60Irr Erdos634.Draft.FDBBaseBetaE1 Erdos634.CertNode Erdos634.CertCoord

theorem TGT_36_10 : dist (Refl.MP120x36.TGT.pts 0) (Refl.MP120x36.TGT.pts 1) = (240 : ℝ) ∧
    dist (Refl.MP120x36.TGT.pts 1) (Refl.MP120x36.TGT.pts 2) = (240 : ℝ) ∧
    dist (Refl.MP120x36.TGT.pts 0) (Refl.MP120x36.TGT.pts 2) = (240 : ℝ) :=
  model_sides_rp Refl.MP120x36.hDn Refl.MP120x36.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(36, 10)`: the rational tile with sides `30, 16` around the angle `π/3` and `26` opposite it,
equilateral target of side `240` (scale `2`); certificate `Refl.MP120x36` -/
theorem pair_36_10 : E60Pair 120 ((36 : ℕ) : ℤ) ((10 : ℕ) : ℤ) := by
  obtain ⟨k1, k2, k3⟩ := Refl.MP120x36.MODEL_sides
  exact e60Pair_of_cert_scaled 120 (by norm_num) _ _ (by norm_num) (by norm_num) (by norm_num) 240
    30 16 26 (by norm_num) (by push_cast; norm_num) (by push_cast; norm_num) (by push_cast; norm_num)
    Refl.MP120x36.TGT Refl.MP120x36.MODEL TGT_36_10
    (fun T h => congruent_of_hasSides' (hasSides_rot (hasSides_rot h)) k1 k2 k3)
    (fun D' hT hM => Refl.MP120x36.not_dissection D' hT hM)

/-- **`GapE60 120`.** -/
theorem gapE60_120 : GapE60 120 := by
  refine gapE60_of_chk_sq (by norm_num) [(36, 10)] (by decide +kernel) ?_
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl
  exact pair_36_10

end Erdos634.Draft.E60N120

#print axioms Erdos634.Draft.E60N120.gapE60_120
