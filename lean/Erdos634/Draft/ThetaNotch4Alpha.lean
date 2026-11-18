-- Draft/ThetaNotch4Alpha.lean -- TASK B (corollaries): alpha_g tiled for g f >= t0f e f; TileCount 2576, 4025, 5796, 7008.  INTERNAL BUILD ONLY, UNAUDITED.
-- No sorry, no native_decide.
/-
`alphaTiled_all`: coprime `1 <= e < f`, `f f = e e + b`, `g >= 1`, `t0f e f <= g f`  ==>  `AlphaTiled e f b g`
(`thetaTiled_all` of `ThetaNotch4Rho` + the hub `alphaTiled_of_thetaTiled` of `ThetaNotch4Glue`).
`tileCount_alpha`: `TileCount (b (b + f f) g g)` for those parameters.
Concrete (alphaonly.txt of internal audit): `2576 = alpha_4(3,4)` (b=7, t0f=14 <= 16), `4025 = alpha_5(3,4)`, `5796 = alpha_6(3,4)`, `7008 = alpha_2(5,7)` (b=24, t0f=13 <= 14).
HYPOTHESES ARE SATISFIED (decide): coprimality, `f f = e e + b`, `t0f e f <= g f`.
CONTROLS (the settled-instances registry, read-only): there is NO `NO_TILING` row for an alpha target at (3,4) or (5,7); the rows for the four N are TILING_EXISTS in the registry since the sweep_night rows citing this file.
The only alpha NO row is `basealpha (2,3) g = 1, N = 70`: the lemma needs `theta_3(2,3)`, and `t0f 2 3 = 7 > 3` (`alpha_control_70`), so it yields nothing there; at (2,3) with
`g f >= 7` it reproduces the known S3 collar tile counts `1120 = alpha_4(2,3)` and `1750 = alpha_5(2,3)` (rows `S3collar`, TILING_EXISTS).  `e = 1`: `g f >= 2 f`, i.e. `g >= 2`,
matching `alpha_exists` on thin rows.  (Correction 2026-11-14, audit note N1b: the registry row `basealpha (1,3) N=34`, target (36,36,68), has K = 4 with b = 8, i.e. g = 1/2; N = 34 is not of the form 136 g^2 for an integer g, so it is not an `AlphaTiled` instance at all; `alpha_control_34` below is a true statement about g = 1, N = 136 only, not about that row.)
CREDIT: the hub gluing is prior art: M. Beeson (arXiv:1206.2229 v5, Cor. 8, Fig. 25; Fig. 23 for (2,3,4)), then D. Paliy (alpha-isosceles construction, 29 Sep 2026);
the 48-tile seed theta_4(1,2) is Beeson (Fig. 16), as are BLZ arXiv:2604.03609 Fig. 4 and Paliy.  Only the four values 2576, 4025, 5796, 7008, which rest on our seeds, are new.
Also Beeson-Rosu, Laczkovich, Zhang as in ThetaNotch4Glue.  INTERNAL BUILD ONLY, UNAUDITED.
-/
import Erdos634.Draft.ThetaNotch4Rho
import Erdos634.Draft.ThetaNotch4Glue

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

namespace Erdos634.Draft.ThetaNotch
noncomputable section
open Erdos634.Draft.ThetaUnit (ThetaTiled)
open Erdos634.Draft.TileCountFamilies (TileCount)

theorem alphaTiled_all (e f b g : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hb : f * f = e * e + b)
    (hg : 1 ≤ g) (hge : t0f e f ≤ g * f) : AlphaTiled e f b g := by
  have hb' : b = f * f - e * e := by omega
  subst hb'
  exact alphaTiled_of_thetaTiled e f _ g he hef hb hg (thetaTiled_all e f he hef hco (g * f) hge)

theorem tileCount_alpha (e f b g : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (hb : f * f = e * e + b)
    (hg : 1 ≤ g) (hge : t0f e f ≤ g * f) : TileCount (b * (b + f * f) * g * g) := by
  obtain ⟨D, -, -⟩ := alphaTiled_all e f b g he hef hco hb hg hge
  exact ⟨D⟩

/-- `2576 = alpha_4(3,4)`, tile `(12, 7, 16)`. -/
theorem tileCount_2576 : TileCount 2576 := by
  have h := tileCount_alpha 3 4 7 4 (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by have := t0f_table.2.2.1; omega)
  norm_num at h; exact h
/-- `4025 = alpha_5(3,4)`. -/
theorem tileCount_4025 : TileCount 4025 := by
  have h := tileCount_alpha 3 4 7 5 (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by have := t0f_table.2.2.1; omega)
  norm_num at h; exact h
/-- `5796 = alpha_6(3,4)`. -/
theorem tileCount_5796 : TileCount 5796 := by
  have h := tileCount_alpha 3 4 7 6 (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by have := t0f_table.2.2.1; omega)
  norm_num at h; exact h
/-- `7008 = alpha_2(5,7)`, tile `(35, 24, 49)`. -/
theorem tileCount_7008 : TileCount 7008 := by
  have h := tileCount_alpha 5 7 24 2 (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by have := t0f_table.2.2.2.2.2.2.1; omega)
  norm_num at h; exact h

/-- hypotheses exhibited: the four parameter sets satisfy `t0f e f <= g f`. -/
theorem alpha_hyp_witnesses : t0f 3 4 ≤ 4 * 4 ∧ t0f 3 4 ≤ 5 * 4 ∧ t0f 3 4 ≤ 6 * 4 ∧ t0f 5 7 ≤ 2 * 7 := by decide

/-- control 1: at `(2,3)` the lemma reproduces the S3 collar tile counts `1120 = alpha_4`, `1750 = alpha_5` (rows `S3collar`, TILING_EXISTS). -/
theorem tileCount_1120 : TileCount 1120 := by
  have h := tileCount_alpha 2 3 5 4 (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by have := t0f_table.2.1; omega)
  norm_num at h; exact h
theorem tileCount_1750 : TileCount 1750 := by
  have h := tileCount_alpha 2 3 5 5 (by norm_num) (by norm_num) (by decide) (by norm_num) (by norm_num)
    (by have := t0f_table.2.1; omega)
  norm_num at h; exact h

/-- control 2: the known-NO target `alpha_1(2,3)` (N = 70): the lemma's hypothesis `t0f <= g f` FAILS there (`1 * 3 < 7`), so it asserts nothing. -/
theorem alpha_control_70 : ¬ (t0f 2 3 ≤ 1 * 3) := by decide
/-- control 3: `alpha_1(1,3)` (g = 1, N = b (b + f^2) g^2 = 8 * 17 = 136): the hypothesis `t0f <= g f` fails, `t0f 1 3 = 6 > 3`.  NOT about registry row N = 34 (target (36,36,68), K = 4, g = 1/2; N = 34 is not of the form 136 g^2, so it is no instance at all). -/
theorem alpha_control_34 : ¬ (t0f 1 3 ≤ 1 * 3) := by decide

end
end Erdos634.Draft.ThetaNotch
