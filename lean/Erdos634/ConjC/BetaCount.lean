/-
ConjC/BetaCount.lean -- the COUNT of the base-β tilings: `M²(3f² − e²)` is a tile count for coprime `1 ≤ e < f`, `M ≥ f`.

`UniformThreshold.BetaTilable e f M` leaves the number of tiles existentially free; `tileCount_beta_seed` gives the
count only at `M = f`.  Here the count is read off the construction: the beta lift `CollarG.beta_lift_real` of a
`W_M` tiling (`(2f² − e²) M²` tiles, `Residue.wTilable_ge`) adds one tile scaled by `Mf`, so the count is
`(2f² − e²) M² + (Mf)² = M²(3f² − e²)`.

THE CONSTRUCTION IS NOT OURS: D. Paliy (collar, beta lift, residue seeds), seed credited by him to M. Beeson.
What is added is the count, from the existing formal proof.  Composite-N statement.  UNAUDITED.  No sorry.
-/
import Erdos634.Draft.ResidueSeed

open scoped Classical
open Erdos634.Geometry Erdos634.CertCoord

namespace Erdos634.ConjC.BetaCount
open Erdos634.Draft.CollarG
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- the count-carrying form of `CollarG.betaTilable_of_wTilable` -/
theorem tileCount_of_wTilable (u g T : ℕ) (hu : 0 < u) (hg : 0 < g) (hT : 0 < T) (h : WTilable u (u + g) T) :
    TileCount ((2 * (u + g) ^ 2 - u ^ 2) * T ^ 2 + T * (u + g) * (T * (u + g))) := by
  have hu' : (0 : ℝ) < u := Nat.cast_pos.mpr hu
  have hg' : (0 : ℝ) < g := Nat.cast_pos.mpr hg
  have hT' : (0 : ℝ) < T := Nat.cast_pos.mpr hT
  obtain ⟨R⟩ := (wTilable_iff_frame u g T hu hg hT).mp h
  obtain ⟨D, -, -⟩ := beta_lift_real hu' hg' hT' (k := T * (u + g)) (Nat.mul_pos hT (by omega))
    (by push_cast; ring) R
  exact ⟨D⟩

/-- **`M²(3f² − e²)` is a tile count** for coprime `1 ≤ e < f` and every `M ≥ f`. -/
theorem tileCount_beta_ge (e f : ℕ) (he : 1 ≤ e) (hef : e < f) (hco : Nat.Coprime e f) (M : ℕ) (hM : f ≤ M) :
    TileCount (M ^ 2 * (3 * f ^ 2 - e ^ 2)) := by
  have hw := Erdos634.Draft.Residue.wTilable_ge e f he hef hco M hM
  obtain ⟨g, rfl⟩ : ∃ g, f = e + g := ⟨f - e, by omega⟩
  have hc := tileCount_of_wTilable e g M (by omega) (by omega) (by omega) hw
  have hle : e ^ 2 ≤ (e + g) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have key : M ^ 2 * (3 * (e + g) ^ 2 - e ^ 2) =
      (2 * (e + g) ^ 2 - e ^ 2) * M ^ 2 + M * (e + g) * (M * (e + g)) := by
    have e1 : 3 * (e + g) ^ 2 - e ^ 2 = (2 * (e + g) ^ 2 - e ^ 2) + (e + g) ^ 2 := by
      generalize (e + g) ^ 2 = V at hle ⊢; generalize e ^ 2 = U at hle ⊢; omega
    rw [e1]; ring
  rw [key]; exact hc

end Erdos634.ConjC.BetaCount
