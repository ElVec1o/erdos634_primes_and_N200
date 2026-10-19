-- Draft/CollarFam5.lean — LOWERED collar tail: TileCount (2485 g²) for ALL g ≥ 5 (was g ≥ 7), from the new seed T62125 (g=5).  UNAUDITED.
-- Seed found by our engine macro search (2026-10-19); layer step as in CollarFam (formalization of Paliy's alpha-isosceles up-set, independent construction).
import Erdos634.Draft.CollarFam
import Erdos634.Draft.T62125

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Erdos634.Draft.CollarFam
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- Base of row (1,6): the template tiling `Erdos634.Draft.T62125` as a region tiling of `T_7`. -/
theorem base_2485_g5 : Nonempty (RTiling (TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((5:ℕ):ℝ)) (Mrow Erdos634.Draft.T62125.hf 1 6 (by norm_num) (by norm_num)) (2485 * 5 * 5)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.T62125.hf) (T := Erdos634.Draft.T62125.tgt) Erdos634.Draft.T62125.regionOf Erdos634.Draft.T62125.cnt Erdos634.Draft.T62125.famAll Erdos634.Draft.T62125.hS_all Erdos634.Draft.T62125.hsub_all Erdos634.Draft.T62125.hvol_all
  have hMeq : Mrow Erdos634.Draft.T62125.hf 1 6 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.T62125.hf := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((5:ℕ):ℝ) = Erdos634.Draft.T62125.tgt.carrier := by
    rw [Erdos634.Draft.T62125.tgt_carrier]; unfold TG pB0 Erdos634.Draft.T62125.tA Erdos634.Draft.T62125.tB Erdos634.Draft.T62125.tC; push_cast; norm_num
  have key : ∀ N : ℕ, N = 2485 * 5 * 5 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.T62125.hf → D.target = Erdos634.Draft.T62125.tgt →
      Nonempty (RTiling (TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((5:ℕ):ℝ)) (Mrow Erdos634.Draft.T62125.hf 1 6 (by norm_num) (by norm_num)) (2485 * 5 * 5)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.T62125.sum_cnt) D hD hT

/-- **Collar up-set, row (1,6):** `2485 g²` is a tile count for every `g ≥ 5`. -/
theorem tileCount_2485_sq5 : ∀ g : ℕ, 5 ≤ g → TileCount (2485 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.T62125.hf 1 6 35 2485 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_2485_g5 g hg
  exact tileCount_of_rtiling Erdos634.Draft.T62125.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R


end
end Erdos634.Draft.CollarFam

#print axioms Erdos634.Draft.CollarFam.tileCount_2485_sq5
