import Erdos634.MarchKills

/-!
# MarchKills — march geometry and tile-killing lemmas: wrapper

Key results:
- `apexH_pos`, `apexH_lt_b`: apex height bounds
- `apexH_lt_overshootH`, `overshootH_lt_strip`: overshoot bounds
- `march_confined`: all march tiles fit within overshoot strip
- `no_bg_then_gb`: BG and GB tiles at adjacent positions cannot coexist
- `far_corner_kill`: the far-corner criterion kills e=1 tilings
- `far_corner_f3`: numerical check at f=3

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MarchKillsWrap

open Erdos634.MarchKills Erdos634.Geometry Erdos634.BaseBetaTargetCoord

theorem mk_apexH_pos {f : ℝ} (hf : 1 < f) : 0 < apexH f :=
  apexH_pos hf

theorem mk_apexH_lt_b {f : ℝ} (hf : 1 < f) : apexH f < f ^ 2 - 1 :=
  apexH_lt_b hf

theorem mk_apexH_lt_overshootH {f : ℝ} (hf : 1 < f) : apexH f < overshootH f :=
  apexH_lt_overshootH hf

theorem mk_overshootH_lt_strip {f : ℝ} (hf : 1 < f) : overshootH f < apexH f + 1 :=
  overshootH_lt_strip hf

theorem mk_no_bg_then_gb {N : ℕ} (D : Dissection N) {f : ℝ} (hf : 1 < f) {i j : Fin N}
    (hij : i ≠ j) {t s : ℝ} (hts : s = t + f)
    (hi : D.tile i = aTileBG t f hf) (hj : D.tile j = aTileGB s f hf) : False :=
  no_bg_then_gb D hf hij hts hi hj

theorem mk_far_corner_kill {N : ℕ} (D : Dissection N) {f : ℝ} (hf : 1 < f)
    (htgt : D.target = baseBetaTarget 1 f one_pos hf)
    {iM j : Fin N} (hne : iM ≠ j)
    (hiM : D.tile iM = aTileBG (baseLen 1 f - 3 * f) f hf)
    (hj : D.tile j = aTileBG (baseLen 1 f - 2 * f) f hf ∨
          D.tile j = aTileGB (baseLen 1 f - 2 * f) f hf) : False :=
  far_corner_kill D hf htgt hne hiM hj

-- far_corner_f3 uses dBG from MarchCoords; delegate directly
theorem mk_far_corner_f3 :
    Erdos634.BaseBetaTargetCoord.baseLen 1 3 - 2 * 3 + Erdos634.MarchCoords.dBG 3 = 73 / 3 ∧
    Erdos634.BaseBetaTargetCoord.baseLen 1 3 -
      Erdos634.BaseBetaTargetCoord.baseLen 1 3 / (2 * 3) = 65 / 3 ∧
    Erdos634.BaseBetaTargetCoord.baseLen 1 3 - 3 * 3 + Erdos634.MarchCoords.dBG 3 = 64 / 3 :=
  far_corner_f3

-- Non-vacuity: apexH 2 > 0
example : (0 : ℝ) < apexH 2 := mk_apexH_pos (by norm_num)

#print axioms mk_apexH_pos
#print axioms mk_far_corner_kill

end Erdos634.Draft.MarchKillsWrap
