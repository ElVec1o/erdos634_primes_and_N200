import Mathlib
import Erdos634.E1BaseWord
import Erdos634.MemberUniform
import Erdos634.MarchCoords
import Erdos634.BaseBetaE1

/-!
# The refutation at every member, as finite statements

The content splits into

* **the refutation exists at every member** — `findep_no_completion`: for every `f ≥ 3` (so at
  `f = 12, 14, …, 22` and every adjacent word `(bp, bp−1)`) there is no congruent dissection of the
  `m = 1`, `e = 1` base-β target by `(f, f²−1, f²)`.  Immediate corollary of
  `E1BaseWord.e1_family_f_ge_3_congruent`.
* **no test distinguishes the members** — `tests_uniform_members`: `MemberUniform.tests_uniform`
  instantiated at the actual tile angles of any two members `f, f' ≥ 2` (hypotheses discharged:
  `3α + 2β = π` by definition of `β`, irrationality by `BaseBetaE1.tile_alpha_irrational`), so the
  theorem is non-vacuous at `f = 12, …, 22`.
* **the placements are `f`-instantiations of one set of coordinates** — `dBG_instances`,
  `h2_eq`: the first apex abscissa `d_BG = (3f²−1)/(2f)` takes the values `431/24` (f = 12) and
  `587/28` (f = 14), and the squared apex height is `((f²−1)/(2f))²·(4f²−1)`.

Not Lean statements (properties of the search program's run): the node counts
`299, 506, 807, 1315, 2124, 3441`, the depth `13`, and "the same tree".

Standard axioms; no `sorry`.
-/

namespace Erdos634.Draft.HeurFinDep

open Real

open Erdos634.Geometry Erdos634.CertCoord Erdos634.MarchKillsFan Erdos634.MarchSlots
  Erdos634.MarchInduction Erdos634.MarchKills Erdos634.BaseBetaTargetCoord Erdos634.MarchCompose in
/-- **No completion at any member** (corollary of `thm:e1family`, `f ≥ 3`). -/
theorem findep_no_completion {N : ℕ} (D₀ : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega)))) :
    False :=
  Erdos634.E1BaseWord.e1_family_f_ge_3_congruent D₀ hn3 htgt hmod

/-- The tile angle `α` of the member `(1, f)`: `sin(α/2) = 1/(2f)`. -/
noncomputable def alphaOf (f : ℕ) : ℝ := 2 * arcsin (1 / (2 * (f : ℝ)))

/-- The tile angle `β` of the member `(1, f)`, from `3α + 2β = π`. -/
noncomputable def betaOf (f : ℕ) : ℝ := (π - 3 * alphaOf f) / 2

theorem rel_of (f : ℕ) : 3 * alphaOf f + 2 * betaOf f = π := by unfold betaOf; ring

theorem irr_of (f : ℕ) (hf : 2 ≤ f) : ¬ ∃ r : ℚ, alphaOf f = (r : ℝ) * π := by
  apply Erdos634.BaseBetaE1.tile_alpha_irrational 1 f le_rfl (by omega)
  have hf' : (2 : ℝ) ≤ f := by exact_mod_cast hf
  have h1 : -1 ≤ 1 / (2 * (f : ℝ)) := by
    have : 0 ≤ 1 / (2 * (f : ℝ)) := by positivity
    linarith
  have h2 : 1 / (2 * (f : ℝ)) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  unfold alphaOf
  rw [mul_div_cancel_left₀ _ (two_ne_zero), sin_arcsin h1 h2]
  push_cast; ring

/-- **Member uniformity at the actual tile angles.**  For any two members `f, f' ≥ 2` (in
particular `f, f' ∈ {12, 14, …, 22}`), a corner `Xα + Yβ` is fillable at `f` iff at `f'`, and the residue-`1` test answers alike. -/
theorem tests_uniform_members (f f' : ℕ) (hf : 2 ≤ f) (hf' : 2 ≤ f') (X Y : ℕ) :
    ((∃ x y z : ℕ, (x : ℝ) * alphaOf f + (y : ℝ) * betaOf f + (z : ℝ) * (2 * alphaOf f + betaOf f)
        = (X : ℝ) * alphaOf f + (Y : ℝ) * betaOf f)
      ↔ (∃ x y z : ℕ, (x : ℝ) * alphaOf f' + (y : ℝ) * betaOf f'
          + (z : ℝ) * (2 * alphaOf f' + betaOf f') = (X : ℝ) * alphaOf f' + (Y : ℝ) * betaOf f'))
    ∧ ((¬ ∃ x y z : ℕ, x * f + y * (f ^ 2 - 1) + z * f ^ 2 = 1)
      ↔ (¬ ∃ x y z : ℕ, x * f' + y * (f' ^ 2 - 1) + z * f' ^ 2 = 1)) :=
  Erdos634.MemberUniform.tests_uniform (rel_of f) (irr_of f hf) (rel_of f') (irr_of f' hf')
    f f' hf hf' X Y

/-- The squared apex height is `((f²−1)/(2f))² · (4f²−1)`: numerator `f²−1` over `2f`,
radicand `4f²−1`. -/
theorem h2_eq (f : ℝ) (hf : f ≠ 0) :
    Erdos634.MarchCoords.h2 f = ((f ^ 2 - 1) / (2 * f)) ^ 2 * (4 * f ^ 2 - 1) := by
  unfold Erdos634.MarchCoords.h2; field_simp; ring

/-- The first apex abscissa at the six members of the table. -/
theorem dBG_instances :
    Erdos634.MarchCoords.dBG 12 = 431 / 24 ∧ Erdos634.MarchCoords.dBG 14 = 587 / 28 ∧
    Erdos634.MarchCoords.dBG 16 = 767 / 32 ∧ Erdos634.MarchCoords.dBG 18 = 971 / 36 ∧
    Erdos634.MarchCoords.dBG 20 = 1199 / 40 ∧ Erdos634.MarchCoords.dBG 22 = 1451 / 44 := by
  unfold Erdos634.MarchCoords.dBG; norm_num

end Erdos634.Draft.HeurFinDep
