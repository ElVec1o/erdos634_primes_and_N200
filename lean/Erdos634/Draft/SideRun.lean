/-
Draft/SideRun.lean -- the final statements for the members `e = 1` of the base-β row, tile `(f, f²−1, f²)`.

* `not_wTilable_e1`: `¬ WTilable 1 f M` for `1 ≤ M < f`;
* `wTilable_e1_iff`: `WTilable 1 f M ↔ f ≤ M` for `f ≥ 2`, `M ≥ 1` (the direction `←` is `Residue.wTilable_ge`,
  the construction of D. Paliy);
* `not_betaTilable_e1_half`: `¬ BetaTilable 1 f M` for `1 ≤ M`, `2M < f`;
  `thresholdAt_e1_half`: the threshold statement at these scales; `not_betaTilable_e1_two`: `M = 2`, `f ≥ 5`;
* sharpness: `wTilable_e1_self` (`WTilable 1 f f`, the seed), `betaTilable_e1_self`;
* `side_theorem_witness`: the hypotheses of the side theorem (`Setup`, `Corners`) hold for a normal form of the seed
  tiling of `W_f(1,f)`, and its side `QB` carries `f` consecutive tiles of type `C1` or of type `C2`.

The proofs are `SideRunMain.no_dissection_W`, `no_dissection_T` (which import no certificate module); this file only
restates them with the definitions `WTilable` (`Draft/CollarG.lean`) and `BetaTilable`, `ThresholdAt`
(`Draft/UniformThreshold.lean`), whose files import other parts of the corpus.

No sorry, no native_decide.
-/
import Erdos634.Draft.SideRunMain
import Erdos634.Draft.UniformThreshold
import Erdos634.Draft.ResidueSeed

namespace Erdos634.Draft.SideRun

open Erdos634.Geometry Erdos634.BaseBetaTargetCoord Erdos634.Draft.FDBBaseBetaE1
  Erdos634.Draft.CollarG Erdos634.Draft.UniformThreshold Erdos634.Draft.W2E1

/-- **THEOREM C.**  For `1 ≤ M < f` the triangle `W_M` of the member `(1, f)` has no tiling. -/
theorem not_wTilable_e1 (f M : ℕ) (hM : 1 ≤ M) (hMf : M < f) : ¬ WTilable 1 f M := by
  rintro ⟨D, hTs, hMs⟩
  refine no_dissection_W f M hM hMf D ?_ ?_
  · exact hasSides_cast' (hasSides_rot (hasSides_rot hTs)) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring)
  · exact hasSides_cast' hMs (by push_cast; ring) (by push_cast; ring) (by ring)

/-- **`W_M` of the member `(1, f)` has a tiling exactly from the scale `f` on.** -/
theorem wTilable_e1_iff (f M : ℕ) (hf : 2 ≤ f) (hM : 1 ≤ M) : WTilable 1 f M ↔ f ≤ M := by
  constructor
  · intro h
    by_contra hc
    exact not_wTilable_e1 f M hM (by omega) h
  · intro h
    exact Erdos634.Draft.Residue.wTilable_ge 1 f le_rfl (by omega) (Nat.coprime_one_left f) M h

/-- **THEOREM B.**  For `1 ≤ M` and `2M < f` the base-β target `T_M` of the member `(1, f)` has no tiling. -/
theorem not_betaTilable_e1_half (f M : ℕ) (hM : 1 ≤ M) (h : 2 * M < f) : ¬ BetaTilable 1 f M := by
  rintro ⟨N, D, hTs, hMs⟩
  refine no_dissection_T f M hM h D ?_ ?_
  · exact hasSides_cast' hTs (by ring) (by ring) (by push_cast; ring)
  · exact hasSides_cast' hMs (by push_cast; ring) (by push_cast; ring) (by ring)

/-- the threshold statement holds at the scales `M < f/2` of the members `(1, f)` -/
theorem thresholdAt_e1_half (f M : ℕ) (hM : 1 ≤ M) (h : 2 * M < f) : ThresholdAt 1 f M :=
  ⟨fun hT => absurd hT (not_betaTilable_e1_half f M hM h), fun hle => absurd hle (by omega)⟩

/-- `T_2(1,f)` has no tiling for `f ≥ 5` (no certificate) -/
theorem not_betaTilable_e1_two (f : ℕ) (hf : 5 ≤ f) : ¬ BetaTilable 1 f 2 :=
  not_betaTilable_e1_half f 2 (by norm_num) (by omega)

/-- sharpness of Theorem C: `W_f(1,f)` has a tiling (the seed) -/
theorem wTilable_e1_self (f : ℕ) (hf : 2 ≤ f) : WTilable 1 f f := wTilable_seed 1 f le_rfl (by omega)

/-- `T_f(1,f)` has a tiling (the seed) -/
theorem betaTilable_e1_self (f : ℕ) (hf : 2 ≤ f) : BetaTilable 1 f f :=
  betaTilable_self le_rfl (by omega)

/-- **The hypotheses of the side theorem are satisfiable, and its conclusion is observed**: a normal form of the
seed tiling of `W_f(1,f)` is a `Setup` with `Corners` (second form), and its side `QB` carries `f` consecutive tiles
of type `C1` or `f` consecutive tiles of type `C2`. -/
theorem side_theorem_witness (f : ℕ) (hf : 2 ≤ f) :
    ∃ (N : ℕ) (D : CongruentDissection N) (L ax ay : ℝ),
      Setup D f (modelAlpha 1 f) (modelBeta 1 f) (2 * modelAlpha 1 f + modelBeta 1 f) L ax ay ∧
      Corners f L ax ay ∧
      ∃ (m : ℕ) (X : ℕ → ℝ) (tile : ℕ → Fin N) (τ : ℕ → Ty), Chain D f L m X tile τ ∧
        ∃ i, i + f ≤ m ∧ ((∀ j, j < f → τ (i + j) = Ty.C1) ∨ (∀ j, j < f → τ (i + j) = Ty.C2)) := by
  obtain ⟨D₀, hTs, hMs⟩ := wTilable_seed 1 f le_rfl (by omega : 1 < f)
  have hf1 : (1:ℝ) < f := by exact_mod_cast (show 1 < f by omega)
  have hfr : (0:ℝ) < f := by linarith
  obtain ⟨D, S⟩ := setup_W f f hf (by omega) D₀
    (hasSides_cast' (hasSides_rot (hasSides_rot hTs)) (by push_cast; ring) (by push_cast; ring)
      (by push_cast; ring))
    (hasSides_cast' hMs (by push_cast; ring) (by push_cast; ring) (by ring))
  have Co := corners_W f f hf1 hfr
  exact ⟨_, D, _, _, _, S, Co, S.side_theorem' Co⟩

end Erdos634.Draft.SideRun

#print axioms Erdos634.Draft.SideRun.not_wTilable_e1
#print axioms Erdos634.Draft.SideRun.wTilable_e1_iff
#print axioms Erdos634.Draft.SideRun.not_betaTilable_e1_half
#print axioms Erdos634.Draft.SideRun.thresholdAt_e1_half
#print axioms Erdos634.Draft.SideRun.not_betaTilable_e1_two
#print axioms Erdos634.Draft.SideRun.wTilable_e1_self
#print axioms Erdos634.Draft.SideRun.side_theorem_witness
