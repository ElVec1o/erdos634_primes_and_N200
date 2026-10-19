-- Draft/CollarFam17.lean — LOWERED collar tail: TileCount (966 g²) for ALL g ≥ 17 (was g ≥ 25), from the new seed TM279174 (g=17, macro chain 3864 -> 15456 -> 24150 -> ... -> 247296).  UNAUDITED.
-- Seeds found by our engine macro-search closure loop (2026-10-19); layer step as in CollarFam (formalization of Paliy's alpha-isosceles up-set, independent construction); macro idea Laczkovich/Herdt.
import Erdos634.Draft.CollarFam
import Erdos634.Draft.TM279174

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Erdos634.Draft.CollarFam
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- Base of row (2,5): the template tiling `Erdos634.Draft.TM279174` as a region tiling of `T_25`. -/
theorem base_966_g17 : Nonempty (RTiling (TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((17:ℕ):ℝ)) (Mrow Erdos634.Draft.TM279174.hf 2 5 (by norm_num) (by norm_num)) (966 * 17 * 17)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.TM279174.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num)) (T := Erdos634.Draft.TM279174.tgt) Erdos634.Draft.TM279174.regionOf Erdos634.Draft.TM279174.cnt Erdos634.Draft.TM279174.famAll Erdos634.Draft.TM279174.hS_all Erdos634.Draft.TM279174.hsub_all Erdos634.Draft.TM279174.hvol_all
  have hMeq : Mrow Erdos634.Draft.TM279174.hf 2 5 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.TM279174.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num) := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((17:ℕ):ℝ) = Erdos634.Draft.TM279174.tgt.carrier := by
    rw [Erdos634.Draft.TM279174.tgt_carrier]; unfold TG pB0 Erdos634.Draft.TM279174.tA Erdos634.Draft.TM279174.tB Erdos634.Draft.TM279174.tC; push_cast
    congr 2; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; norm_num
  have key : ∀ N : ℕ, N = 966 * 17 * 17 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.TM279174.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num) → D.target = Erdos634.Draft.TM279174.tgt →
      Nonempty (RTiling (TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((17:ℕ):ℝ)) (Mrow Erdos634.Draft.TM279174.hf 2 5 (by norm_num) (by norm_num)) (966 * 17 * 17)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.TM279174.sum_cnt) D hD hT

/-- **Collar up-set, row (2,5):** `966 g²` is a tile count for every `g ≥ 17`. -/
theorem tileCount_966_sq17 : ∀ g : ℕ, 17 ≤ g → TileCount (966 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.TM279174.hf 2 5 21 966 17 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_966_g17 g hg
  exact tileCount_of_rtiling Erdos634.Draft.TM279174.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R


end
end Erdos634.Draft.CollarFam

#print axioms Erdos634.Draft.CollarFam.tileCount_966_sq17
