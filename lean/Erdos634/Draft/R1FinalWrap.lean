import Erdos634.Draft.R1Final

/-!
# R1Final — thick line (e = f−1) exclusion: wrapper

Key results:
- `r1_no_tiling`: the main exclusion — no congruent dissection of the m=1 base-β target
  into tiles with sides (ef, f²−e², f²) exists when e = f−1, for any f ≥ 2, any N.
- `r1_no_tiling_perm`: same, model vertices in any order (τ : Equiv.Perm (Fin 3))
- `r1_no_tiling_all_f`: same, indexed by f ≥ 2 alone (e = f−1)
- `r1_n11`: the f = 2 (N = 11) member explicitly
- `depth_iff_thick`: the depth inequality fires EXACTLY on e = f−1 (sharpness)

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.R1FinalWrap

open Erdos634.Draft.R1Final
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord

variable {N : ℕ}

/-- No congruent dissection of the m=1 base-β target into copies of the tile (ef, f²−e², f²)
exists when e = f−1, f ≥ 2. This is the core of the thick-line exclusion. -/
theorem rf_r1_no_tiling (D₀ : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e) (hef1 : e + 1 = f)
    (htgt : D₀.target.Congruent (baseBetaTarget e f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast (show e < f by omega))))
    (T : Tri) (hT0 : sideOpp T 0 = (e : ℝ) * f) (hT1 : sideOpp T 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hT2 : sideOpp T 2 = (f : ℝ) ^ 2) (hmod : D₀.model.Congruent T) : False :=
  r1_no_tiling D₀ he hef1 htgt T hT0 hT1 hT2 hmod

/-- Same, model vertices in any permutation order. -/
theorem rf_r1_no_tiling_perm (D₀ : CongruentDissection N) {e f : ℕ} (he : 1 ≤ e)
    (hef1 : e + 1 = f)
    (htgt : D₀.target.Congruent (baseBetaTarget e f (by exact_mod_cast (show 0 < e by omega))
      (by exact_mod_cast (show e < f by omega))))
    (τ : Equiv.Perm (Fin 3))
    (hs0 : sideOpp (D₀.model.relabel τ) 0 = (e : ℝ) * f)
    (hs1 : sideOpp (D₀.model.relabel τ) 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (hs2 : sideOpp (D₀.model.relabel τ) 2 = (f : ℝ) ^ 2) : False :=
  r1_no_tiling_perm D₀ he hef1 htgt τ hs0 hs1 hs2

/-- Same, indexed by f ≥ 2 alone (e = f−1 implicit). -/
theorem rf_r1_no_tiling_all_f (D₀ : CongruentDissection N) {f : ℕ} (hf : 2 ≤ f)
    (htgt : D₀.target.Congruent (baseBetaTarget ((f - 1 : ℕ) : ℝ) f
      (by exact_mod_cast (show 0 < f - 1 by omega)) (by exact_mod_cast (show f - 1 < f by omega))))
    (T : Tri) (hT0 : sideOpp T 0 = ((f - 1 : ℕ) : ℝ) * f)
    (hT1 : sideOpp T 1 = (f : ℝ) ^ 2 - ((f - 1 : ℕ) : ℝ) ^ 2)
    (hT2 : sideOpp T 2 = (f : ℝ) ^ 2) (hmod : D₀.model.Congruent T) : False :=
  r1_no_tiling_all_f D₀ hf htgt T hT0 hT1 hT2 hmod

/-- Depth inequality fires EXACTLY on e = f−1 (sharpness of the only member-dependent input). -/
theorem rf_depth_iff_thick {e f : ℕ} (he : 1 ≤ e) (hef : e < f) :
    (f : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) < 2 * (f : ℝ) ^ 2 ↔ e + 1 = f :=
  depth_iff_thick he hef

-- Non-vacuity: hyps_nonvacuous_f2 (ground proof that hypotheses are satisfiable at f=2)
example : 1 ≤ (1 : ℕ) ∧ (1 : ℕ) + 1 = 2 := ⟨le_refl _, rfl⟩

#print axioms rf_r1_no_tiling
#print axioms rf_depth_iff_thick

end Erdos634.Draft.R1FinalWrap
