-- Draft/CollarFam465.lean — 465 g² is a tile count for ALL g ≥ 2 (tile (4,15,16), row (e,f)=(1,4), b=15, N0=15*(15+16)=465).  UNAUDITED.
-- Seed: TM1860 (T_2, 6 convex lattice-run pieces; template tiling found by the template engine / bto, 2026-10-20), then the collar layer step (CollarLayer.layer_core)
--   valid at every base g0 >= 1 when e f <= f²-e²: 1*4 <= 15, 4*4 = 1+15, phi = 4/1.   g=1 (N=465) is NOT covered (not a tile count by this route).
--   Instances: g=2 (1860), 3 (4185), 4 (7440), 5 (11625; also Draft/T11625 and CollarFam5).
-- CREDIT: formalization of Paliy's alpha up-set (docs/eventual-rational-families.md, 2026-09-29; K>=ceil(B/v)), an independent construction;
-- the collar/layer analysis (project working notes); Beeson-Rosu (skew frame S2L, Thm 10/24); Laczkovich/Herdt macro-dissections; the template engine.
import Erdos634.Draft.CollarFam
import Erdos634.Draft.TM1860

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Erdos634.Draft.CollarFam465
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer Erdos634.Draft.CollarFam
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- Base of row (1,4): the template tiling `Erdos634.Draft.TM1860` as a region tiling of `T_2`. -/
theorem base_465_g2 : Nonempty (RTiling (TG 4 ((1:ℕ):ℝ) ((4:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM1860.hf 1 4 (by norm_num) (by norm_num)) (465 * 2 * 2)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.MF 4 Erdos634.Draft.TM1860.hf) (T := Erdos634.Draft.TM1860.tgt) Erdos634.Draft.TM1860.regionOf Erdos634.Draft.TM1860.cnt Erdos634.Draft.TM1860.famAll Erdos634.Draft.TM1860.hS_all Erdos634.Draft.TM1860.hsub_all Erdos634.Draft.TM1860.hvol_all
  have hMeq : Mrow Erdos634.Draft.TM1860.hf 1 4 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.MF 4 Erdos634.Draft.TM1860.hf := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG 4 ((1:ℕ):ℝ) ((4:ℕ):ℝ) ((2:ℕ):ℝ) = Erdos634.Draft.TM1860.tgt.carrier := by
    rw [Erdos634.Draft.TM1860.tgt_carrier]; unfold TG pB0 Erdos634.Draft.TM1860.tA Erdos634.Draft.TM1860.tB Erdos634.Draft.TM1860.tC; push_cast; norm_num
  have key : ∀ N : ℕ, N = 465 * 2 * 2 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.MF 4 Erdos634.Draft.TM1860.hf → D.target = Erdos634.Draft.TM1860.tgt →
      Nonempty (RTiling (TG 4 ((1:ℕ):ℝ) ((4:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM1860.hf 1 4 (by norm_num) (by norm_num)) (465 * 2 * 2)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.TM1860.sum_cnt) D hD hT

/-- **Collar up-set, row (1,4):** `465 g²` is a tile count for every `g ≥ 2`. -/
theorem tileCount_465_sq2 : ∀ g : ℕ, 2 ≤ g → TileCount (465 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.TM1860.hf 1 4 15 465 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_465_g2 g hg
  exact tileCount_of_rtiling Erdos634.Draft.TM1860.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R



theorem tileCount_465_sq_ge2 : ∀ g : ℕ, 2 ≤ g → TileCount (465 * g ^ 2) := by
  intro g hg
  have := tileCount_465_sq2 g hg
  rwa [show 465 * g * g = 465 * g ^ 2 by ring] at this

theorem tileCount_1860' : TileCount 1860 := by simpa using tileCount_465_sq_ge2 2 le_rfl
theorem tileCount_4185' : TileCount 4185 := by simpa using tileCount_465_sq_ge2 3 (by norm_num)
theorem tileCount_7440' : TileCount 7440 := by simpa using tileCount_465_sq_ge2 4 (by norm_num)
theorem tileCount_11625' : TileCount 11625 := by simpa using tileCount_465_sq_ge2 5 (by norm_num)

end
end Erdos634.Draft.CollarFam465

#print axioms Erdos634.Draft.TM1860.tileCount_1860
#print axioms Erdos634.Draft.CollarFam465.tileCount_465_sq_ge2
#print axioms Erdos634.Draft.CollarFam465.tileCount_4185'
#print axioms Erdos634.Draft.CollarFam465.tileCount_7440'
#print axioms Erdos634.Draft.CollarFam465.tileCount_11625'
