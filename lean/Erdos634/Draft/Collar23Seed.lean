-- Draft/Collar23Seed.lean -- THE SEED: T(12) (base 180, legs 120, N = 720) is tiled by 720 copies of the tile (4,5,6), kernel-checked;
-- hence Tile23 g for ALL g >= 12 (collar23), i.e. 5 g^2 is a tile count of (4,5,6)-isosceles triangles T(g) for every g >= 12.
-- UNAUDITED.  No sorry, no native_decide (decide +kernel only).  NOT imported by All.
-- What is checked by what: (a) Python (gen/emit_seed.py) re-checked the table before generation; (b) the Lean KERNEL checks, for the
-- 720-entry table `seedTab0` (Collar23SeedTab, generated from the engine file S2/til_720.txt): model sides, non-degeneracy,
-- containment (Collar23SeedChk), a separating edge line for each of the 258,840 pairs (Collar23SeedP01..P09, row chunks),
-- total area; (c) the covering is NOT pointwise but from AREA (ConvexCover.covers_of_volume) in Collar23SeedLib.seedRT.
-- Credit: B. Herdt (the 720-layout generalising Beeson 1206.1974v7 Fig. 24), Beeson-Rosu, Paliy (collar idea); strip/cap/slice: the project's AI assistant P1.
import Erdos634.Draft.Collar23SeedP01
import Erdos634.Draft.Collar23SeedP02
import Erdos634.Draft.Collar23SeedP03
import Erdos634.Draft.Collar23SeedP04
import Erdos634.Draft.Collar23SeedP05
import Erdos634.Draft.Collar23SeedP06
import Erdos634.Draft.Collar23SeedP07
import Erdos634.Draft.Collar23SeedP08
import Erdos634.Draft.Collar23SeedP09
import Erdos634.Draft.Collar23SeedLib

open Erdos634.Geometry
open Erdos634.Draft.TileCountFamilies (TileCount)

namespace Erdos634.Draft.Collar23

theorem rows_ok (a k : ℕ) (h : rowsOK a k = true) (m : ℕ) (h1 : a ≤ m) (h2 : m < a + k) : rowOK m = true := by
  unfold rowsOK at h
  rw [List.all_eq_true] at h
  exact h m (List.mem_range'.mpr ⟨m - a, by omega, by omega⟩)

theorem rowOK_all (m : ℕ) : rowOK m = true :=
  if h720 : 720 ≤ m then by
    unfold rowOK
    have : seedTab0.drop m = [] := List.drop_of_length_le (by rw [seed_len]; exact h720)
    rw [this]
  else by
    have : m < 720 := by omega
    exact if h14 : m < 14 then rows_ok _ _ rows_0_14 m (by omega) (by omega)
    else if h28 : m < 28 then rows_ok _ _ rows_14_14 m (by omega) (by omega)
    else if h42 : m < 42 then rows_ok _ _ rows_28_14 m (by omega) (by omega)
    else if h56 : m < 56 then rows_ok _ _ rows_42_14 m (by omega) (by omega)
    else if h71 : m < 71 then rows_ok _ _ rows_56_15 m (by omega) (by omega)
    else if h86 : m < 86 then rows_ok _ _ rows_71_15 m (by omega) (by omega)
    else if h101 : m < 101 then rows_ok _ _ rows_86_15 m (by omega) (by omega)
    else if h117 : m < 117 then rows_ok _ _ rows_101_16 m (by omega) (by omega)
    else if h133 : m < 133 then rows_ok _ _ rows_117_16 m (by omega) (by omega)
    else if h150 : m < 150 then rows_ok _ _ rows_133_17 m (by omega) (by omega)
    else if h167 : m < 167 then rows_ok _ _ rows_150_17 m (by omega) (by omega)
    else if h185 : m < 185 then rows_ok _ _ rows_167_18 m (by omega) (by omega)
    else if h204 : m < 204 then rows_ok _ _ rows_185_19 m (by omega) (by omega)
    else if h223 : m < 223 then rows_ok _ _ rows_204_19 m (by omega) (by omega)
    else if h243 : m < 243 then rows_ok _ _ rows_223_20 m (by omega) (by omega)
    else if h264 : m < 264 then rows_ok _ _ rows_243_21 m (by omega) (by omega)
    else if h286 : m < 286 then rows_ok _ _ rows_264_22 m (by omega) (by omega)
    else if h309 : m < 309 then rows_ok _ _ rows_286_23 m (by omega) (by omega)
    else if h334 : m < 334 then rows_ok _ _ rows_309_25 m (by omega) (by omega)
    else if h360 : m < 360 then rows_ok _ _ rows_334_26 m (by omega) (by omega)
    else if h388 : m < 388 then rows_ok _ _ rows_360_28 m (by omega) (by omega)
    else if h419 : m < 419 then rows_ok _ _ rows_388_31 m (by omega) (by omega)
    else if h454 : m < 454 then rows_ok _ _ rows_419_35 m (by omega) (by omega)
    else if h494 : m < 494 then rows_ok _ _ rows_454_40 m (by omega) (by omega)
    else if h543 : m < 543 then rows_ok _ _ rows_494_49 m (by omega) (by omega)
    else if h613 : m < 613 then rows_ok _ _ rows_543_70 m (by omega) (by omega)
    else if h720 : m < 720 then rows_ok _ _ rows_613_107 m (by omega) (by omega)
    else by omega

theorem seed_pairwise : seedTab0.Pairwise sep := pairwise_of_rows rowOK_all

/-- **The seed**: `T(12)` is tiled by 720 copies of (4,5,6). -/
theorem tile23_12 : Tile23 12 := seedRT seedTab0 seed_len seed_good seed_pairwise seed_area

/-- **collar23, unconditional**: `T(g)` is tiled by `5 g^2` copies of (4,5,6) for every `g >= 12`. -/
theorem collar23 (g : ℕ) (hg : 12 ≤ g) : Tile23 g := tile23_up 12 (by norm_num) tile23_12 g hg

theorem collar23_dissection (g : ℕ) (hg : 12 ≤ g) :
    ∃ D : CongruentDissection (5 * (g * g)),
      D.target = tri23 (g : ℝ) (by exact_mod_cast (by omega : 0 < g)) ∧ D.model = M23 :=
  collar23_family 12 (by norm_num) tile23_12 g hg (by omega)

theorem collar23_tileCount_all (g : ℕ) (hg : 12 ≤ g) : TileCount (5 * (g * g)) :=
  collar23_tileCount 12 (by norm_num) tile23_12 g hg

#print axioms seed_pairwise
#print axioms tile23_12
#print axioms collar23
#print axioms collar23_dissection
#print axioms collar23_tileCount_all

end Erdos634.Draft.Collar23
