-- Draft/CollarUp.lean — THEOREM A + the e = 1 up-set:  for every f ≥ 2 and g ≥ f+1,  TileCount ((f²−1)(2f²−1) g²).  UNAUDITED.
-- No sorry, no native_decide.
--   Seed:   CollarSeed.seed_core  (6-piece template, coordinates polynomial in f, tiles T(f+1)),
--   Step:   CollarFam.layer_step  (T_G ⇒ T_{G+1}, valid for e f ≤ f²−e², in particular e = 1, f ≥ 2).
-- Witnesses (non-vacuity): f=2,g=3 → 189;  f=4,g=5 → 11625;  f=4,g=6 → 16740;  f=6,g=7 → 121765;  f=6,g=8 → 159040.
-- CREDIT: formalization of Paliy's alpha up-set (docs/eventual-rational-families.md, 2026-09-29), an independent construction;
-- 84 and 189 are Beeson's (v4 Figs 28–29, 189 credited to Harries).  Ours: parametric seed (Theorem A), collar/layer mechanism
-- ((project working notes)) and the Lean proofs.  Macro-dissection idea: Laczkovich;
-- skew frame S2L: Beeson–Roșu.
import Erdos634.Draft.CollarSeed

open scoped Classical
open Erdos634.Geometry

set_option linter.unusedVariables false

namespace Erdos634.Draft.CollarUp
noncomputable section
open Erdos634.Draft.CollarFam Erdos634.Draft.CollarLayer Erdos634.Draft.RegionTiling
open Erdos634.Draft.TileCountFamilies (TileCount)

/-- **Theorem A (e = 1 seed)** in naturals: `T(f+1)` of the row `(1,f)` is tiled. -/
theorem seed_rtiling (f b : ℕ) (hf : 2 ≤ f) (hb : f * f = 1 + b) :
    ∃ hφ : (1 : ℝ) < (f : ℝ),
      Nonempty (RTiling (TG (f : ℝ) ((1 : ℕ) : ℝ) (f : ℝ) (((f + 1 : ℕ)) : ℝ)) (Mrow hφ 1 f (by norm_num) (by omega))
        (b * (b + f * f) * (f + 1) * (f + 1))) := by
  have hfR : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have hφ : (1 : ℝ) < (f : ℝ) := by linarith
  refine ⟨hφ, ?_⟩
  have hbR : (b : ℝ) = (f : ℝ) ^ 2 - 1 := by
    have : ((f * f : ℕ) : ℝ) = ((1 + b : ℕ) : ℝ) := by rw [hb]
    push_cast at this; nlinarith
  have hfb : f ≤ b := by nlinarith
  have h := CollarSeed.seed_core (F := (f : ℝ)) hfR hφ (f * f) (b * (f + 1)) (b * b) (b * b - f) (f * b) (f * f) b (b - f)
    (b * (b + f * f)) (f + 1)
    (by push_cast; ring) (by push_cast; rw [hbR]) (by push_cast; rw [hbR]; ring)
    (by rw [Nat.cast_sub (by nlinarith)]; push_cast; rw [hbR]; ring) (by push_cast; rw [hbR]) (by push_cast; ring)
    (by rw [hbR]) (by rw [Nat.cast_sub hfb, hbR]) (Nat.sub_le _ _) (Nat.sub_le _ _)
    (by push_cast; rw [hbR]; ring) (by push_cast; ring)
  simpa [Mrow] using h

/-- **The e = 1 collar up-set.**  For every `f ≥ 2` and `g ≥ f+1`, `(f²−1)(2f²−1) g²` is a tile count
(tile `(f, f²−1, f²)`, base-α isosceles target). -/
theorem tileCount_e1_up (f g : ℕ) (hf : 2 ≤ f) (hg : f + 1 ≤ g) :
    TileCount ((f * f - 1) * (2 * (f * f) - 1) * (g * g)) := by
  obtain ⟨b, hb⟩ : ∃ b, f * f = 1 + b := by
    have : 1 ≤ f * f := by nlinarith
    exact ⟨f * f - 1, by omega⟩
  have hN : (f * f - 1) * (2 * (f * f) - 1) * (g * g) = b * (b + f * f) * g * g := by
    have h1 : f * f - 1 = b := by omega
    have h2 : 2 * (f * f) - 1 = b + f * f := by omega
    rw [h1, h2]; ring
  rw [hN]
  obtain ⟨hφ, base⟩ := seed_rtiling f b hf hb
  have hba : 1 * f ≤ b := by nlinarith
  obtain ⟨R⟩ := up_rtiling hφ 1 f b (b * (b + f * f)) (f + 1) (by norm_num) (by omega) (by omega) hba
    (by simp) rfl (by omega) base g hg
  exact tileCount_of_rtiling hφ (E := ((1 : ℕ) : ℝ)) (by norm_num) (by exact_mod_cast (show 1 < f by omega))
    (g := (g : ℝ)) (by exact_mod_cast (show 0 < g by omega)) R

theorem tileCount_189 : TileCount 189 := by simpa using tileCount_e1_up 2 3 le_rfl (by norm_num)
theorem tileCount_16740 : TileCount 16740 := by simpa using tileCount_e1_up 4 6 (by norm_num) (by norm_num)
theorem tileCount_159040 : TileCount 159040 := by simpa using tileCount_e1_up 6 8 (by norm_num) (by norm_num)

end
end Erdos634.Draft.CollarUp

#print axioms Erdos634.Draft.CollarUp.seed_rtiling
#print axioms Erdos634.Draft.CollarUp.tileCount_e1_up
#print axioms Erdos634.Draft.CollarUp.tileCount_189
#print axioms Erdos634.Draft.CollarUp.tileCount_16740
#print axioms Erdos634.Draft.CollarUp.tileCount_159040
