-- Draft/DebtBWTilable.lean -- DEBT_B (2026-10-19), UNAUDITED.  No sorry, no native_decide.
/-
**The thirteen W-family tilings below the threshold, as `WTilable e f M0` (target-shaped), and their upward closure.**

For each of the thirteen `(N, e, f, M0)` of `AllWBelow` (`Draft/TW<N>.lean`): `WTilable e f M0` (the triangle with sides
`M0 f (f²-e²), M0 e (2f²-e²), M0 f³` is cut into `(2f²-e²) M0²` copies of the tile `(ef, f²-e², f²)`), obtained from the
packing of `TW<N>` through `DebtB.wTilable_of_pack`; and, by `DebtB.counts_of_wTilable` (`f ≤ M0 (f-e)` holds in all
thirteen), for all `M ≥ M0`: `WTilable e f M`, `TileCount ((2f²-e²) M²)` and `TileCount (M² (3f²-e²))`.

Credits: D. Paliy (W/beta framework, collar and layer ideas, upward closure in M); M. Beeson and I. Rosu (S2L skew frame);
our collar/strip sessions (`CollarG`, `WStripChord`); templates from our engine `bto`.
-/
import Erdos634.Draft.DebtBBridge
import Erdos634.Draft.AllWBelow

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)
open Erdos634.Draft.WBrickF (brickL)
open Erdos634.Draft.CollarG (WTilable)
open Erdos634.Draft.TileCountFamilies (TileCount)
open Erdos634.Draft.UniformThreshold (hasSides_congr)
open Erdos634.Draft.DebtB
open Erdos634.Draft.LadderFam (pack_exists')

set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace Erdos634.Draft.DebtB

theorem wTilable_656 : WTilable 3 5 4 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (5/3:ℝ) T656.hf (15:ℝ) (16:ℝ) (by norm_num) (by norm_num))
    (T := T656.tgt) T656.regionOf T656.cnt T656.famAll T656.hS_all T656.hsub_all T656.hvol_all
  refine wTilable_of_pack (e := 3) (f := 5) (M := 4) (N := ∑ a, T656.cnt a) (by norm_num) (by norm_num)
    (by rw [T656.sum_cnt]; norm_num) (F := (5/3:ℝ)) (by norm_num) T656.hf (15:ℝ) (16:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T656.tgt hT hD ?_
  have hs : HasSides T656.tgt (320:ℝ) (492:ℝ) (500:ℝ) := by
    unfold T656.tgt
    exact hasSides_triC_o1 T656.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T656.tA, T656.tB]) (by norm_num [sqf, T656.tB, T656.tC]) (by norm_num [sqf, T656.tC, T656.tA])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_656 : ∀ M, 4 ≤ M → WTilable 3 5 M ∧ TileCount ((2 * 5 ^ 2 - 3 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 5 ^ 2 - 3 ^ 2)) :=
  counts_of_wTilable 3 5 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_656

theorem wTilable_1312 : WTilable 4 7 4 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (7/4:ℝ) T1312.hf (28:ℝ) (33:ℝ) (by norm_num) (by norm_num))
    (T := T1312.tgt) T1312.regionOf T1312.cnt T1312.famAll T1312.hS_all T1312.hsub_all T1312.hvol_all
  refine wTilable_of_pack (e := 4) (f := 7) (M := 4) (N := ∑ a, T1312.cnt a) (by norm_num) (by norm_num)
    (by rw [T1312.sum_cnt]; norm_num) (F := (7/4:ℝ)) (by norm_num) T1312.hf (28:ℝ) (33:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T1312.tgt hT hD ?_
  have hs : HasSides T1312.tgt (924:ℝ) (1312:ℝ) (1372:ℝ) := by
    unfold T1312.tgt
    exact hasSides_triC_o1 T1312.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T1312.tA, T1312.tB]) (by norm_num [sqf, T1312.tB, T1312.tC]) (by norm_num [sqf, T1312.tC, T1312.tA])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_1312 : ∀ M, 4 ≤ M → WTilable 4 7 M ∧ TileCount ((2 * 7 ^ 2 - 4 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 7 ^ 2 - 4 ^ 2)) :=
  counts_of_wTilable 4 7 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_1312

theorem wTilable_1648 : WTilable 5 8 4 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (8/5:ℝ) T1648.hf (40:ℝ) (39:ℝ) (by norm_num) (by norm_num))
    (T := T1648.tgt) T1648.regionOf T1648.cnt T1648.famAll T1648.hS_all T1648.hsub_all T1648.hvol_all
  refine wTilable_of_pack (e := 5) (f := 8) (M := 4) (N := ∑ a, T1648.cnt a) (by norm_num) (by norm_num)
    (by rw [T1648.sum_cnt]; norm_num) (F := (8/5:ℝ)) (by norm_num) T1648.hf (40:ℝ) (39:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T1648.tgt hT hD ?_
  have hs : HasSides T1648.tgt (1248:ℝ) (2060:ℝ) (2048:ℝ) := by
    unfold T1648.tgt
    exact hasSides_triC_base T1648.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T1648.tB, T1648.tC]) (by norm_num [sqf, T1648.tC, T1648.tA]) (by norm_num [sqf, T1648.tA, T1648.tB])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_1648 : ∀ M, 4 ≤ M → WTilable 5 8 M ∧ TileCount ((2 * 8 ^ 2 - 5 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 8 ^ 2 - 5 ^ 2)) :=
  counts_of_wTilable 5 8 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_1648

theorem wTilable_1825 : WTilable 5 7 5 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (7/5:ℝ) T1825.hf (35:ℝ) (24:ℝ) (by norm_num) (by norm_num))
    (T := T1825.tgt) T1825.regionOf T1825.cnt T1825.famAll T1825.hS_all T1825.hsub_all T1825.hvol_all
  refine wTilable_of_pack (e := 5) (f := 7) (M := 5) (N := ∑ a, T1825.cnt a) (by norm_num) (by norm_num)
    (by rw [T1825.sum_cnt]; norm_num) (F := (7/5:ℝ)) (by norm_num) T1825.hf (35:ℝ) (24:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T1825.tgt hT hD ?_
  have hs : HasSides T1825.tgt (840:ℝ) (1825:ℝ) (1715:ℝ) := by
    unfold T1825.tgt
    exact hasSides_triC_base T1825.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T1825.tB, T1825.tC]) (by norm_num [sqf, T1825.tC, T1825.tA]) (by norm_num [sqf, T1825.tA, T1825.tB])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_1825 : ∀ M, 5 ≤ M → WTilable 5 7 M ∧ TileCount ((2 * 7 ^ 2 - 5 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 7 ^ 2 - 5 ^ 2)) :=
  counts_of_wTilable 5 7 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_1825

theorem wTilable_1953 : WTilable 5 11 3 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (11/5:ℝ) T1953.hf (55:ℝ) (96:ℝ) (by norm_num) (by norm_num))
    (T := T1953.tgt) T1953.regionOf T1953.cnt T1953.famAll T1953.hS_all T1953.hsub_all T1953.hvol_all
  refine wTilable_of_pack (e := 5) (f := 11) (M := 3) (N := ∑ a, T1953.cnt a) (by norm_num) (by norm_num)
    (by rw [T1953.sum_cnt]; norm_num) (F := (11/5:ℝ)) (by norm_num) T1953.hf (55:ℝ) (96:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T1953.tgt hT hD ?_
  have hs : HasSides T1953.tgt (3168:ℝ) (3255:ℝ) (3993:ℝ) := by
    unfold T1953.tgt
    exact hasSides_triC_o1 T1953.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T1953.tA, T1953.tB]) (by norm_num [sqf, T1953.tB, T1953.tC]) (by norm_num [sqf, T1953.tC, T1953.tA])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_1953 : ∀ M, 3 ≤ M → WTilable 5 11 M ∧ TileCount ((2 * 11 ^ 2 - 5 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 11 ^ 2 - 5 ^ 2)) :=
  counts_of_wTilable 5 11 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_1953

theorem wTilable_2192 : WTilable 5 9 4 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (9/5:ℝ) T2192.hf (45:ℝ) (56:ℝ) (by norm_num) (by norm_num))
    (T := T2192.tgt) T2192.regionOf T2192.cnt T2192.famAll T2192.hS_all T2192.hsub_all T2192.hvol_all
  refine wTilable_of_pack (e := 5) (f := 9) (M := 4) (N := ∑ a, T2192.cnt a) (by norm_num) (by norm_num)
    (by rw [T2192.sum_cnt]; norm_num) (F := (9/5:ℝ)) (by norm_num) T2192.hf (45:ℝ) (56:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T2192.tgt hT hD ?_
  have hs : HasSides T2192.tgt (2016:ℝ) (2740:ℝ) (2916:ℝ) := by
    unfold T2192.tgt
    exact hasSides_triC_o1 T2192.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T2192.tA, T2192.tB]) (by norm_num [sqf, T2192.tB, T2192.tC]) (by norm_num [sqf, T2192.tC, T2192.tA])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_2192 : ∀ M, 4 ≤ M → WTilable 5 9 M ∧ TileCount ((2 * 9 ^ 2 - 5 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 9 ^ 2 - 5 ^ 2)) :=
  counts_of_wTilable 5 9 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_2192

theorem wTilable_3088 : WTilable 7 11 4 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (11/7:ℝ) T3088.hf (77:ℝ) (72:ℝ) (by norm_num) (by norm_num))
    (T := T3088.tgt) T3088.regionOf T3088.cnt T3088.famAll T3088.hS_all T3088.hsub_all T3088.hvol_all
  refine wTilable_of_pack (e := 7) (f := 11) (M := 4) (N := ∑ a, T3088.cnt a) (by norm_num) (by norm_num)
    (by rw [T3088.sum_cnt]; norm_num) (F := (11/7:ℝ)) (by norm_num) T3088.hf (77:ℝ) (72:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T3088.tgt hT hD ?_
  have hs : HasSides T3088.tgt (3168:ℝ) (5404:ℝ) (5324:ℝ) := by
    unfold T3088.tgt
    exact hasSides_triC_base T3088.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T3088.tB, T3088.tC]) (by norm_num [sqf, T3088.tC, T3088.tA]) (by norm_num [sqf, T3088.tA, T3088.tB])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_3088 : ∀ M, 4 ≤ M → WTilable 7 11 M ∧ TileCount ((2 * 11 ^ 2 - 7 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 11 ^ 2 - 7 ^ 2)) :=
  counts_of_wTilable 7 11 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_3088

theorem wTilable_3296 : WTilable 6 11 4 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (11/6:ℝ) T3296.hf (66:ℝ) (85:ℝ) (by norm_num) (by norm_num))
    (T := T3296.tgt) T3296.regionOf T3296.cnt T3296.famAll T3296.hS_all T3296.hsub_all T3296.hvol_all
  refine wTilable_of_pack (e := 6) (f := 11) (M := 4) (N := ∑ a, T3296.cnt a) (by norm_num) (by norm_num)
    (by rw [T3296.sum_cnt]; norm_num) (F := (11/6:ℝ)) (by norm_num) T3296.hf (66:ℝ) (85:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T3296.tgt hT hD ?_
  have hs : HasSides T3296.tgt (3740:ℝ) (4944:ℝ) (5324:ℝ) := by
    unfold T3296.tgt
    exact hasSides_triC_o1 T3296.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T3296.tA, T3296.tB]) (by norm_num [sqf, T3296.tB, T3296.tC]) (by norm_num [sqf, T3296.tC, T3296.tA])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_3296 : ∀ M, 4 ≤ M → WTilable 6 11 M ∧ TileCount ((2 * 11 ^ 2 - 6 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 11 ^ 2 - 6 ^ 2)) :=
  counts_of_wTilable 6 11 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_3296

theorem wTilable_3775 : WTilable 7 10 5 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (10/7:ℝ) T3775.hf (70:ℝ) (51:ℝ) (by norm_num) (by norm_num))
    (T := T3775.tgt) T3775.regionOf T3775.cnt T3775.famAll T3775.hS_all T3775.hsub_all T3775.hvol_all
  refine wTilable_of_pack (e := 7) (f := 10) (M := 5) (N := ∑ a, T3775.cnt a) (by norm_num) (by norm_num)
    (by rw [T3775.sum_cnt]; norm_num) (F := (10/7:ℝ)) (by norm_num) T3775.hf (70:ℝ) (51:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T3775.tgt hT hD ?_
  have hs : HasSides T3775.tgt (2550:ℝ) (5285:ℝ) (5000:ℝ) := by
    unfold T3775.tgt
    exact hasSides_triC_base T3775.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T3775.tB, T3775.tC]) (by norm_num [sqf, T3775.tC, T3775.tA]) (by norm_num [sqf, T3775.tA, T3775.tB])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_3775 : ∀ M, 5 ≤ M → WTilable 7 10 M ∧ TileCount ((2 * 10 ^ 2 - 7 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 10 ^ 2 - 7 ^ 2)) :=
  counts_of_wTilable 7 10 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_3775

theorem wTilable_3824 : WTilable 7 12 4 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (12/7:ℝ) T3824.hf (84:ℝ) (95:ℝ) (by norm_num) (by norm_num))
    (T := T3824.tgt) T3824.regionOf T3824.cnt T3824.famAll T3824.hS_all T3824.hsub_all T3824.hvol_all
  refine wTilable_of_pack (e := 7) (f := 12) (M := 4) (N := ∑ a, T3824.cnt a) (by norm_num) (by norm_num)
    (by rw [T3824.sum_cnt]; norm_num) (F := (12/7:ℝ)) (by norm_num) T3824.hf (84:ℝ) (95:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T3824.tgt hT hD ?_
  have hs : HasSides T3824.tgt (4560:ℝ) (6692:ℝ) (6912:ℝ) := by
    unfold T3824.tgt
    exact hasSides_triC_o1 T3824.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T3824.tA, T3824.tB]) (by norm_num [sqf, T3824.tB, T3824.tC]) (by norm_num [sqf, T3824.tC, T3824.tA])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_3824 : ∀ M, 4 ≤ M → WTilable 7 12 M ∧ TileCount ((2 * 12 ^ 2 - 7 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 12 ^ 2 - 7 ^ 2)) :=
  counts_of_wTilable 7 12 4 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_3824

theorem wTilable_4068 : WTilable 7 9 6 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (9/7:ℝ) T4068.hf (63:ℝ) (32:ℝ) (by norm_num) (by norm_num))
    (T := T4068.tgt) T4068.regionOf T4068.cnt T4068.famAll T4068.hS_all T4068.hsub_all T4068.hvol_all
  refine wTilable_of_pack (e := 7) (f := 9) (M := 6) (N := ∑ a, T4068.cnt a) (by norm_num) (by norm_num)
    (by rw [T4068.sum_cnt]; norm_num) (F := (9/7:ℝ)) (by norm_num) T4068.hf (63:ℝ) (32:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T4068.tgt hT hD ?_
  have hs : HasSides T4068.tgt (1728:ℝ) (4746:ℝ) (4374:ℝ) := by
    unfold T4068.tgt
    exact hasSides_triC_base T4068.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T4068.tB, T4068.tC]) (by norm_num [sqf, T4068.tC, T4068.tA]) (by norm_num [sqf, T4068.tA, T4068.tB])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_4068 : ∀ M, 6 ≤ M → WTilable 7 9 M ∧ TileCount ((2 * 9 ^ 2 - 7 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 9 ^ 2 - 7 ^ 2)) :=
  counts_of_wTilable 7 9 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_4068

theorem wTilable_4450 : WTilable 8 11 5 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (11/8:ℝ) T4450.hf (88:ℝ) (57:ℝ) (by norm_num) (by norm_num))
    (T := T4450.tgt) T4450.regionOf T4450.cnt T4450.famAll T4450.hS_all T4450.hsub_all T4450.hvol_all
  refine wTilable_of_pack (e := 8) (f := 11) (M := 5) (N := ∑ a, T4450.cnt a) (by norm_num) (by norm_num)
    (by rw [T4450.sum_cnt]; norm_num) (F := (11/8:ℝ)) (by norm_num) T4450.hf (88:ℝ) (57:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T4450.tgt hT hD ?_
  have hs : HasSides T4450.tgt (3135:ℝ) (7120:ℝ) (6655:ℝ) := by
    unfold T4450.tgt
    exact hasSides_triC_base T4450.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T4450.tB, T4450.tC]) (by norm_num [sqf, T4450.tC, T4450.tA]) (by norm_num [sqf, T4450.tA, T4450.tB])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_4450 : ∀ M, 5 ≤ M → WTilable 8 11 M ∧ TileCount ((2 * 11 ^ 2 - 8 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 11 ^ 2 - 8 ^ 2)) :=
  counts_of_wTilable 8 11 5 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_4450

theorem wTilable_7889 : WTilable 9 11 7 := by
  obtain ⟨D, hD, hT⟩ := pack_exists' (M := brickL (11/9:ℝ) T7889.hf (99:ℝ) (40:ℝ) (by norm_num) (by norm_num))
    (T := T7889.tgt) T7889.regionOf T7889.cnt T7889.famAll T7889.hS_all T7889.hsub_all T7889.hvol_all
  refine wTilable_of_pack (e := 9) (f := 11) (M := 7) (N := ∑ a, T7889.cnt a) (by norm_num) (by norm_num)
    (by rw [T7889.sum_cnt]; norm_num) (F := (11/9:ℝ)) (by norm_num) T7889.hf (99:ℝ) (40:ℝ) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) D T7889.tgt hT hD ?_
  have hs : HasSides T7889.tgt (3080:ℝ) (10143:ℝ) (9317:ℝ) := by
    unfold T7889.tgt
    exact hasSides_triC_base T7889.hf _ _ _ _ (by norm_num) (by norm_num) (by norm_num) (by norm_num [sqf, T7889.tB, T7889.tC]) (by norm_num [sqf, T7889.tC, T7889.tA]) (by norm_num [sqf, T7889.tA, T7889.tB])
  exact hasSides_congr hs (by norm_num) (by norm_num) (by norm_num)

theorem closure_7889 : ∀ M, 7 ≤ M → WTilable 9 11 M ∧ TileCount ((2 * 11 ^ 2 - 9 ^ 2) * M ^ 2) ∧
    TileCount (M ^ 2 * (3 * 11 ^ 2 - 9 ^ 2)) :=
  counts_of_wTilable 9 11 7 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) wTilable_7889

end Erdos634.Draft.DebtB

#print axioms Erdos634.Draft.DebtB.wTilable_656
#print axioms Erdos634.Draft.DebtB.closure_656
#print axioms Erdos634.Draft.DebtB.wTilable_1312
#print axioms Erdos634.Draft.DebtB.closure_1312
#print axioms Erdos634.Draft.DebtB.wTilable_1648
#print axioms Erdos634.Draft.DebtB.closure_1648
#print axioms Erdos634.Draft.DebtB.wTilable_1825
#print axioms Erdos634.Draft.DebtB.closure_1825
#print axioms Erdos634.Draft.DebtB.wTilable_1953
#print axioms Erdos634.Draft.DebtB.closure_1953
#print axioms Erdos634.Draft.DebtB.wTilable_2192
#print axioms Erdos634.Draft.DebtB.closure_2192
#print axioms Erdos634.Draft.DebtB.wTilable_3088
#print axioms Erdos634.Draft.DebtB.closure_3088
#print axioms Erdos634.Draft.DebtB.wTilable_3296
#print axioms Erdos634.Draft.DebtB.closure_3296
#print axioms Erdos634.Draft.DebtB.wTilable_3775
#print axioms Erdos634.Draft.DebtB.closure_3775
#print axioms Erdos634.Draft.DebtB.wTilable_3824
#print axioms Erdos634.Draft.DebtB.closure_3824
#print axioms Erdos634.Draft.DebtB.wTilable_4068
#print axioms Erdos634.Draft.DebtB.closure_4068
#print axioms Erdos634.Draft.DebtB.wTilable_4450
#print axioms Erdos634.Draft.DebtB.closure_4450
#print axioms Erdos634.Draft.DebtB.wTilable_7889
#print axioms Erdos634.Draft.DebtB.closure_7889
