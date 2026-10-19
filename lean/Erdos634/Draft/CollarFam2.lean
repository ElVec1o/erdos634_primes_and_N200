-- Draft/CollarFam2.lean — collar tails lowered to g ≥ 2: TileCount (966 g²) and TileCount (2485 g²) for ALL g ≥ 2.  UNAUDITED.
-- Seeds: TM3864 (row (2,5), tile (10,21,25), T_2) and TM9940 (row (1,6), tile (6,35,36), T_2), template tilings found by our engine bto (2026-10-19).
-- Step: CollarFam.up_rtiling / CollarLayer.layer_core, valid at every base g0 >= 1 when e f <= f^2-e^2:
--   (2,5): b=21, 5*5=2*2+21, 2*5<=21, N0=21*(21+25)=966;  (1,6): b=35, 36=1+35, 6<=35, N0=35*71=2485.   g=1 is NOT covered.
-- CREDIT: formalization of Paliy's alpha up-set (docs/eventual-rational-families.md, 2026-09-29; thresholds K>=17), an independent construction;
-- the collar/layer session (project working notes), AUDIT_COLLAR); Beeson-Rosu (skew frame S2L, Thm 10/24); Laczkovich/Herdt macro-dissections.
import Erdos634.Draft.CollarFam
import Erdos634.Draft.TM3864
import Erdos634.Draft.TM9940

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
namespace Erdos634.Draft.CollarFam2
noncomputable section
open Erdos634.Draft.WFrameF Erdos634.Draft.RegionTiling Erdos634.Draft.WBrickF Erdos634.Draft.CollarLayer Erdos634.Draft.CollarFam
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- Base of row (2,5): the template tiling `Erdos634.Draft.TM3864` as a region tiling of `T_25`. -/
theorem base_966_g2 : Nonempty (RTiling (TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM3864.hf 2 5 (by norm_num) (by norm_num)) (966 * 2 * 2)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.TM3864.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num)) (T := Erdos634.Draft.TM3864.tgt) Erdos634.Draft.TM3864.regionOf Erdos634.Draft.TM3864.cnt Erdos634.Draft.TM3864.famAll Erdos634.Draft.TM3864.hS_all Erdos634.Draft.TM3864.hsub_all Erdos634.Draft.TM3864.hvol_all
  have hMeq : Mrow Erdos634.Draft.TM3864.hf 2 5 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.TM3864.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num) := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((2:ℕ):ℝ) = Erdos634.Draft.TM3864.tgt.carrier := by
    rw [Erdos634.Draft.TM3864.tgt_carrier]; unfold TG pB0 Erdos634.Draft.TM3864.tA Erdos634.Draft.TM3864.tB Erdos634.Draft.TM3864.tC; push_cast
    congr 2; ext x; simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; norm_num
  have key : ∀ N : ℕ, N = 966 * 2 * 2 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.brickL (5/2:ℝ) Erdos634.Draft.TM3864.hf (21:ℝ) (10:ℝ) (by norm_num) (by norm_num) → D.target = Erdos634.Draft.TM3864.tgt →
      Nonempty (RTiling (TG (5/2:ℝ) ((2:ℕ):ℝ) ((5:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM3864.hf 2 5 (by norm_num) (by norm_num)) (966 * 2 * 2)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.TM3864.sum_cnt) D hD hT

/-- **Collar up-set, row (2,5):** `966 g²` is a tile count for every `g ≥ 2`. -/
theorem tileCount_966_sq2 : ∀ g : ℕ, 2 ≤ g → TileCount (966 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.TM3864.hf 2 5 21 966 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_966_g2 g hg
  exact tileCount_of_rtiling Erdos634.Draft.TM3864.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R


/-- Base of row (1,6): the template tiling `Erdos634.Draft.TM9940` as a region tiling of `T_7`. -/
theorem base_2485_g2 : Nonempty (RTiling (TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM9940.hf 1 6 (by norm_num) (by norm_num)) (2485 * 2 * 2)) := by
  obtain ⟨D, hD, hT⟩ := Erdos634.Draft.LadderFam.pack_exists' (M := Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.TM9940.hf) (T := Erdos634.Draft.TM9940.tgt) Erdos634.Draft.TM9940.regionOf Erdos634.Draft.TM9940.cnt Erdos634.Draft.TM9940.famAll Erdos634.Draft.TM9940.hS_all Erdos634.Draft.TM9940.hsub_all Erdos634.Draft.TM9940.hvol_all
  have hMeq : Mrow Erdos634.Draft.TM9940.hf 1 6 (by norm_num) (by norm_num) = Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.TM9940.hf := by
    unfold Mrow; try unfold Erdos634.Draft.WBrickF.MF
    congr 1 <;> norm_num
  have hTeq : TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((2:ℕ):ℝ) = Erdos634.Draft.TM9940.tgt.carrier := by
    rw [Erdos634.Draft.TM9940.tgt_carrier]; unfold TG pB0 Erdos634.Draft.TM9940.tA Erdos634.Draft.TM9940.tB Erdos634.Draft.TM9940.tC; push_cast; norm_num
  have key : ∀ N : ℕ, N = 2485 * 2 * 2 → ∀ D : CongruentDissection N, D.model = Erdos634.Draft.WBrickF.MF 6 Erdos634.Draft.TM9940.hf → D.target = Erdos634.Draft.TM9940.tgt →
      Nonempty (RTiling (TG 6 ((1:ℕ):ℝ) ((6:ℕ):ℝ) ((2:ℕ):ℝ)) (Mrow Erdos634.Draft.TM9940.hf 1 6 (by norm_num) (by norm_num)) (2485 * 2 * 2)) := by
    rintro N rfl D hm ht
    exact rtiling_of_dissection D (hm.trans hMeq.symm) (by rw [ht, hTeq])
  exact key _ (Erdos634.Draft.TM9940.sum_cnt) D hD hT

/-- **Collar up-set, row (1,6):** `2485 g²` is a tile count for every `g ≥ 5`. -/
theorem tileCount_2485_sq2 : ∀ g : ℕ, 2 ≤ g → TileCount (2485 * g * g) := by
  intro g hg
  obtain ⟨R⟩ := up_rtiling Erdos634.Draft.TM9940.hf 1 6 35 2485 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) base_2485_g2 g hg
  exact tileCount_of_rtiling Erdos634.Draft.TM9940.hf (by norm_num) (by norm_num) (by exact_mod_cast (show 0 < g by omega)) R



theorem tileCount_966_sq_ge2 : ∀ g : ℕ, 2 ≤ g → TileCount (966 * g ^ 2) := by
  intro g hg
  have := tileCount_966_sq2 g hg
  rwa [show 966 * g * g = 966 * g ^ 2 by ring] at this

theorem tileCount_2485_sq_ge2 : ∀ g : ℕ, 2 ≤ g → TileCount (2485 * g ^ 2) := by
  intro g hg
  have := tileCount_2485_sq2 g hg
  rwa [show 2485 * g * g = 2485 * g ^ 2 by ring] at this

theorem tileCount_3864' : TileCount 3864 := by simpa using tileCount_966_sq_ge2 2 le_rfl
theorem tileCount_8694' : TileCount 8694 := by simpa using tileCount_966_sq_ge2 3 (by norm_num)
theorem tileCount_279174' : TileCount 279174 := by simpa using tileCount_966_sq_ge2 17 (by norm_num)
theorem tileCount_9940' : TileCount 9940 := by simpa using tileCount_2485_sq_ge2 2 le_rfl
theorem tileCount_22365' : TileCount 22365 := by simpa using tileCount_2485_sq_ge2 3 (by norm_num)
theorem tileCount_718165' : TileCount 718165 := by simpa using tileCount_2485_sq_ge2 17 (by norm_num)

end
end Erdos634.Draft.CollarFam2

#print axioms Erdos634.Draft.CollarFam2.tileCount_966_sq_ge2
#print axioms Erdos634.Draft.CollarFam2.tileCount_2485_sq_ge2
#print axioms Erdos634.Draft.CollarFam2.tileCount_279174'
#print axioms Erdos634.Draft.CollarFam2.tileCount_718165'
