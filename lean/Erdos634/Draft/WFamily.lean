-- `7 m²` is a tile count for every `m ≥ 2`
-- (W-addition from the certified seeds 28 and 63).
import Erdos634.Draft.WSeed
import Erdos634.Draft.TileCountFamilies

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WFamily
open Erdos634.Draft.WFrame Erdos634.Draft.RegionTiling Erdos634.Draft.WBrick Erdos634.Draft.WAdd
  Erdos634.Draft.WSeed

theorem W_all (n : ℕ) :
    Nonempty (RTiling (Phi '' Wt ((n : ℝ) + 2)) MW (7 * (n + 2) ^ 2)) ∧
    Nonempty (RTiling (Phi '' Wt (((n + 1 : ℕ) : ℝ) + 2)) MW (7 * (n + 1 + 2) ^ 2)) := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · obtain ⟨R⟩ := seed28
      exact ⟨RTiling.castN (by norm_num) (RTiling.cast (by norm_num) R)⟩
    · obtain ⟨R⟩ := seed63
      exact ⟨RTiling.castN (by norm_num) (RTiling.cast (by push_cast; norm_num) R)⟩
  | succ n ih =>
    obtain ⟨h0, h1⟩ := ih
    refine ⟨h1, ?_⟩
    obtain ⟨RA⟩ := h0
    obtain ⟨RS⟩ := seed28
    have RA' : RTiling (Phi '' Wt (((n + 1 : ℕ) : ℝ) + 1)) MW (7 * (n + 2) ^ 2) :=
      RTiling.cast (by
        have : ((n + 1 : ℕ) : ℝ) + 1 = (n : ℝ) + 2 := by push_cast; ring
        rw [this]) RA
    have RS' : RTiling (Phi '' Wt (((1 : ℕ) : ℝ) + 1)) MW 28 :=
      RTiling.cast (by norm_num) RS
    have R := wadd (n + 1) 1 RA' RS'
    exact ⟨RTiling.castN (by ring) (RTiling.cast (by
      have : (((n + 1 : ℕ) : ℝ) + 1) + (((1 : ℕ) : ℝ) + 1) = ((n + 1 + 1 : ℕ) : ℝ) + 2 := by
        push_cast; ring
      rw [this]) R)⟩

/-- **`7 m²` is a tile count for every `m ≥ 2`.** -/
theorem tileCount_seven_sq {m : ℕ} (hm : 2 ≤ m) :
    Erdos634.Draft.TileCountFamilies.TileCount (7 * (m * m)) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 2 := ⟨m - 2, by omega⟩
  obtain ⟨R⟩ := (W_all n).1
  have hR : RTiling (Wtri ((n : ℝ) + 2) (by positivity)).carrier MW (7 * (n + 2) ^ 2) :=
    RTiling.cast (carrier_Wtri _ _).symm R
  have : 7 * (n + 2) ^ 2 = 7 * ((n + 2) * (n + 2)) := by ring
  rw [← this]
  exact ⟨toCD hR⟩

end Erdos634.Draft.WFamily

#print axioms Erdos634.Draft.WFamily.tileCount_seven_sq
