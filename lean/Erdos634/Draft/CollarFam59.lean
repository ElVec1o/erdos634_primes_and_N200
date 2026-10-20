-- Draft/CollarFam59.lean — 7672 g² is a tile count for ALL g ≥ 2 (tile (45,56,81), S3 row (e,f)=(5,9), b=56, N0=56*(56+81)=7672).  UNAUDITED.
-- Seed: TM30688 (6 convex lattice-run pieces; template tiling found by the template engine / bto in the overnight sweep, 2026-10-20), then the collar layer step
--   (CollarLayer.layer_core) valid at every base g0 >= 1 when e f <= f²-e²: 5*9 = 45 <= 56, 9*9 = 25+56, phi = 9/5.
--   g=1 (N=7672) is NOT covered by this route.  Instances: g=2 (30688), 3 (69048), 4 (122752), 5 (191800), 6 (276192), 7 (375928).
-- CREDIT: formalization of Paliy's alpha up-set (docs/eventual-rational-families.md, 2026-09-29; his bound for this row is K >= 153, so g = 2..152 lies below his threshold),
-- an independent construction; the collar/layer analysis (project working notes); Beeson-Rosu (skew frame S2L, Thm 10/24);
-- Laczkovich/Herdt macro-dissections; the template engine and the overnight sweep.
import Erdos634.Draft.CollarFam
import Erdos634.Draft.TM30688

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Erdos634.Draft.CollarFam59
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer Erdos634.Draft.CollarFam
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- Base of row (5,9): the template tiling `Erdos634.Draft.TM30688` as a region tiling of `T_2`. -/
theorem base_7672_g2 : Nonempty (RTiling (TG (9/5:ℝ) ((5:ℕ):ℝ) ((9:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM30688.hf 5 9 (by norm_num) (by norm_num)) (7672 * 2 * 2)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.brickL (9/5:ℝ) Erdos634.Draft.TM30688.hf (56:ℝ) (45:ℝ) (by norm_num) (by norm_num)) (T := Erdos634.Draft.TM30688.tgt) Erdos634.Draft.TM30688.regionOf Erdos634.Draft.TM30688.cnt Erdos634.Draft.TM30688.famAll Erdos634.Draft.TM30688.hS_all Erdos634.Draft.TM30688.hsub_all Erdos634.Draft.TM30688.hvol_all
  have hMeq : Mrow Erdos634.Draft.TM30688.hf 5 9 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.brickL (9/5:ℝ) Erdos634.Draft.TM30688.hf (56:ℝ) (45:ℝ) (by norm_num) (by norm_num) := by
    unfold Mrow
    congr 1 <;> norm_num
  have hTeq : TG (9/5:ℝ) ((5:ℕ):ℝ) ((9:ℕ):ℝ) ((2:ℕ):ℝ) = Erdos634.Draft.TM30688.tgt.carrier := by
    rw [Erdos634.Draft.TM30688.tgt_carrier]; unfold TG pB0 Erdos634.Draft.TM30688.tA Erdos634.Draft.TM30688.tB Erdos634.Draft.TM30688.tC; push_cast
    congr 2; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; norm_num
  have key : ∀ N : ℕ, N = 7672 * 2 * 2 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.brickL (9/5:ℝ) Erdos634.Draft.TM30688.hf (56:ℝ) (45:ℝ) (by norm_num) (by norm_num) → D.target = Erdos634.Draft.TM30688.tgt →
      Nonempty (RTiling (TG (9/5:ℝ) ((5:ℕ):ℝ) ((9:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM30688.hf 5 9 (by norm_num) (by norm_num)) (7672 * 2 * 2)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.TM30688.sum_cnt) D hD hT

/-- **Collar up-set, row (5,9):** `7672 g²` is a tile count for every `g ≥ 2`. -/
theorem tileCount_7672_sq2 : ∀ g : ℕ, 2 ≤ g → TileCount (7672 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.TM30688.hf 5 9 56 7672 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_7672_g2 g hg
  exact tileCount_of_rtiling Erdos634.Draft.TM30688.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R

theorem tileCount_7672_sq_ge2 : ∀ g : ℕ, 2 ≤ g → TileCount (7672 * g ^ 2) := by
  intro g hg
  have := tileCount_7672_sq2 g hg
  rwa [show 7672 * g * g = 7672 * g ^ 2 by ring] at this

theorem tileCount_30688' : TileCount 30688 := by simpa using tileCount_7672_sq_ge2 2 le_rfl
theorem tileCount_69048' : TileCount 69048 := by simpa using tileCount_7672_sq_ge2 3 (by norm_num)
theorem tileCount_122752' : TileCount 122752 := by simpa using tileCount_7672_sq_ge2 4 (by norm_num)
theorem tileCount_191800' : TileCount 191800 := by simpa using tileCount_7672_sq_ge2 5 (by norm_num)
theorem tileCount_276192' : TileCount 276192 := by simpa using tileCount_7672_sq_ge2 6 (by norm_num)
theorem tileCount_375928' : TileCount 375928 := by simpa using tileCount_7672_sq_ge2 7 (by norm_num)

end
end Erdos634.Draft.CollarFam59

#print axioms Erdos634.Draft.TM30688.tileCount_30688
#print axioms Erdos634.Draft.CollarFam59.tileCount_7672_sq_ge2
#print axioms Erdos634.Draft.CollarFam59.tileCount_69048'
#print axioms Erdos634.Draft.CollarFam59.tileCount_375928'
