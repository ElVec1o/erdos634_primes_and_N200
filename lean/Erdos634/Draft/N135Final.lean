/-
Draft/N135Final.lean -- `135` is not a tile count (closed statement), from the kernel-checked certificate `Refl.MEQ135`.

    theorem e120pair_135_15_27 : E120Pair 135 15 27
    theorem e120pair_135_27_15 : E120Pair 135 27 15
    theorem not_tile_135 (D : CongruentDissection 135) : False
    theorem not_tileCount_135 : ¬ TileCount 135

`Draft.N135.not_tile_135_of` reduces `135` to one instance: the equilateral triangle of side `45 l` and the tile
`l · (3, 5, 7)` (the pairs `(15, 27)` and `(27, 15)` of the `2π/3` relation name the same tile).  That instance is
refuted by `Refl.MEQ135.not_dissection`, a free-branch-point certificate written by `rust/certgenx` in MIRROR mode:
subtrees only for the two root placements with the angle `α` on the base; the two with the angle `β` on the base are
refuted through their mirror images (`Refl.sound_mirror`).

Prior art: the exclusion of `135` is announced by D. Paliy (ledger: `15 m²` is a tile count
exactly for `m ≥ 4`, with an LRAT certificate for the residual case of `135`); unrefereed.  What is here is a
certificate checked by the Lean kernel and a closed Lean statement.  There is no analytic bound in the literature
for this case: see `Draft.N240` (the side `60` is tiled).

The certificate is not imported by `Erdos634.All` (aggregate: `Erdos634.AllCert5`).  No sorry, no native_decide.
-/
import Erdos634.Draft.GapE120Exc
import Erdos634.Draft.N135Red
import Erdos634.Refl.MEQ135Sound

open scoped Classical
open Erdos634.Geometry Erdos634.CertNode Erdos634.CertCoord
open Erdos634.Draft.Chain15 Erdos634.Draft.TheoremPConditional Erdos634.Draft.CompositeE5Gen
open Erdos634.Draft.GapE120Exc

namespace Erdos634.Draft.N135F

theorem TGT135_sides : dist (Refl.MEQ135.TGT.pts 0) (Refl.MEQ135.TGT.pts 1) = 45 ∧
    dist (Refl.MEQ135.TGT.pts 1) (Refl.MEQ135.TGT.pts 2) = 45 ∧
    dist (Refl.MEQ135.TGT.pts 0) (Refl.MEQ135.TGT.pts 2) = 45 :=
  model_sides_rp Refl.MEQ135.hDn Refl.MEQ135.TGT_pos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

/-- the pair `(15, 27)`: tile `l · (5, 3, 7)` in the order of the relation, side `45 l` -/
theorem e120pair_135_15_27 : E120Pair 135 15 27 := by
  intro D α a b c hα h hE h1 h2 harea
  have hS0 := D.target.oppLen_pos 0
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  push_cast at h1 h2 harea
  obtain ⟨hc, ha', hb'⟩ := shape_of_pair (D.target.oppLen 0) a b c 15 27 135 45 7 2 8 hS0 ha hb (by norm_num)
    (by norm_num) h1 h2 harea (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact close_of_cert D hα h hE Refl.MEQ135.TGT Refl.MEQ135.MODEL 45 3 5 7 (D.target.oppLen 0 / 45) (by positivity)
    TGT135_sides Refl.MEQ135.MODEL_sides (by ring) hc (Or.inl ⟨by rw [hb']; ring, by rw [ha']; ring⟩)
    (fun D' hT hM => Refl.MEQ135.not_dissection D' hT hM)

/-- the pair `(27, 15)`: the same tile with `a` and `b` exchanged -/
theorem e120pair_135_27_15 : E120Pair 135 27 15 := by
  intro D α a b c hα h hE h1 h2 harea
  have hS0 := D.target.oppLen_pos 0
  obtain ⟨t1, t2, t3⟩ := h.tri_ineq
  have ha : 0 < a := by linarith
  have hb : 0 < b := by linarith
  push_cast at h1 h2 harea
  obtain ⟨hc, ha', hb'⟩ := shape_of_pair (D.target.oppLen 0) a b c 27 15 135 45 7 (-2) 8 hS0 ha hb (by norm_num)
    (by norm_num) h1 h2 harea (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact close_of_cert D hα h hE Refl.MEQ135.TGT Refl.MEQ135.MODEL 45 3 5 7 (D.target.oppLen 0 / 45) (by positivity)
    TGT135_sides Refl.MEQ135.MODEL_sides (by ring) hc (Or.inr ⟨by rw [ha']; ring, by rw [hb']; ring⟩)
    (fun D' hT hM => Refl.MEQ135.not_dissection D' hT hM)

/-- **`135` is not a tile count.** -/
theorem not_tile_135 (D : CongruentDissection 135) : False :=
  Erdos634.Draft.N135.not_tile_135_of e120pair_135_15_27 e120pair_135_27_15 D

theorem not_tileCount_135 : ¬ Erdos634.Draft.TileCountFamilies.TileCount 135 :=
  fun ⟨D⟩ => not_tile_135 D

end Erdos634.Draft.N135F

#print axioms Erdos634.Draft.N135F.not_tile_135
#print axioms Erdos634.Draft.N135F.not_tileCount_135
