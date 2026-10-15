import Erdos634.Draft.BaseBetaFullUnc
/-!
# Consequences of `basebeta_full_unc` for base-β dissections

Since `basebeta_full_unc` proves `False` for any base-β `CongruentDissection`,
every statement whose hypotheses include a base-β tiling holds vacuously.
Each proof below is a single application of `basebeta_full_unc`.
The Lean statements are stronger than the structural statements they correspond to (Lean proves `False`).
-/

namespace Erdos634.Draft.VacuousCompanionWrap

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.BaseBetaTargetCoord
open Erdos634.Draft.BaseBetaFullUnc

/-!
## Shorthand: base-β hypothesis bundle

All vacuous theorems take the same 6 hypotheses as `basebeta_full_unc`.
We name the bundle to avoid repeating the htgt/h0/h1/h2 pattern each time.
-/

/-- Any base-β CongruentDissection yields False (direct corollary of basebeta_full_unc).
    All theorems in this file follow by `False.elim` from this. -/
theorem base_beta_false {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega))
        (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  basebeta_full_unc D hco he hef htgt h0 h1 h2

/-!
## thm:walls13 — Hypothesis~\ref{hyp:walls} holds at (1,3)
Paper statement: "No tiling of the (1,3) target at m=1 carries an a-edge on an equal side.
Hence no tiling of the (1,3) target at m=1 exists at all."
Lean: False (from e1_family_f_ge_3 at f=3, packaged via basebeta_full_unc). STRONGER.
-/
theorem walls13_no_tiling {N : ℕ} (D : CongruentDissection N)
    (htgt : D.target.Congruent (baseBetaTarget (1 : ℝ) 3 (by norm_num) (by norm_num)))
    (h0 : sideOpp D.model 0 = (3 : ℝ))
    (h1 : sideOpp D.model 1 = (8 : ℝ))
    (h2 : sideOpp D.model 2 = (9 : ℝ)) : False := by
  apply basebeta_full_unc (e := 1) (f := 3) D (by decide) le_rfl (by norm_num)
  · convert htgt using 2 <;> norm_num
  · norm_num [h0]
  · norm_num [h1]
  · norm_num [h2]

/-!
## thm:walls14 — Hypothesis~\ref{hyp:walls} holds at (1,4)
Paper: "Hypothesis (walls) holds at (1,4)."
Lean: False (from e1_family_f_ge_3 at f=4, via basebeta_full_unc). STRONGER.
-/
theorem walls14_no_tiling {N : ℕ} (D : CongruentDissection N)
    (htgt : D.target.Congruent (baseBetaTarget (1 : ℝ) 4 (by norm_num) (by norm_num)))
    (h0 : sideOpp D.model 0 = (4 : ℝ))
    (h1 : sideOpp D.model 1 = (15 : ℝ))
    (h2 : sideOpp D.model 2 = (16 : ℝ)) : False := by
  apply basebeta_full_unc (e := 1) (f := 4) D (by decide) le_rfl (by norm_num)
  · convert htgt using 2 <;> norm_num
  · norm_num [h0]
  · norm_num [h1]
  · norm_num [h2]

/-!
## lem:ple — Two c-edges are forced; p ≤ f-2
Paper: "At e=1, m=1, the first and last edges of each equal side are c-edges; p ≤ f-2."
Lean: False for any (e,f) base-β tiling (stronger). STRONGER.
-/
theorem lem_ple_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## lem:interior — Interior multiples
Paper: "A base edge of length f²-1 or f² placed with its left end below f² contains a
multiple of f in its open interior... the letters covering [0,f²) are exactly f copies of a."
Lean: False for any base-β tiling. STRONGER.
-/
theorem lem_interior_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## thm:forkkill — The row fork kill
Paper: "The row fork kills the A₂ branch" (requires brick/mate language in paper).
Lean: False for any base-β tiling — no fork configuration can exist. STRONGER.
-/
theorem thm_forkkill_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## lem:termwedge — Terminal wedge
Paper: "The terminal wedge of a base-reaching column decomposes as {γ,α,β}."
Arithmetic kernels: termwedge_alpha_beta_corner, termwedge_boundary_cases (already in Draft).
Lean: False for any base-β tiling — no base-reaching column can exist. STRONGER.
-/
theorem lem_termwedge_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## Offset congruence
Column offset arithmetic.
Lean: `False` for any base-β tiling.
-/
theorem lem_offsets_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## prop:gammagrading — γ-grading
Paper: "Every edge direction in a base-β tiling is an integer multiple of γ."
Lean: False for any base-β tiling — no such tiling to grade. STRONGER.
-/
theorem prop_gammagrading_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## prop:dirgroup — Direction group
Paper: "The direction group ℤ²/⟨p,q⟩ classifies branches."
Lean: False for any base-β tiling. STRONGER.
-/
theorem prop_dirgroup_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## thm:ray — The mismatch ray is completely determined
Paper: incommensurable branch mismatch ray arithmetic.
Lean: False for any base-β tiling. STRONGER.
-/
theorem thm_ray_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## cor:farvacuous — The far side can never give a contradiction
Paper: "The far side can never give a contradiction."
Lean: False for any base-β tiling. STRONGER.
-/
theorem cor_farvacuous_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

/-!
## thm:farregion — The far region is a scaled tile
Paper: "The far region of an incommensurable branch tiling is a scaled tile."
Lean: False for any base-β tiling. STRONGER.
-/
theorem thm_farregion_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2


-- shared proof abbreviation
private abbrev vac_proof {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  base_beta_false D hco he hef htgt h0 h1 h2

theorem lem_eastfan_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_a2branch_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_topjunction_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_walkstruct_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_pentagon_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_apexconfig_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_wallclimb_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_l2slot_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_elltwo_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_depthwindow_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_pierce_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_doublec_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_filler_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_rung2_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_walls16_no_tiling {N : ℕ} (D : CongruentDissection N)
    (htgt : D.target.Congruent (baseBetaTarget (1 : ℝ) 6 (by norm_num) (by norm_num)))
    (h0 : sideOpp D.model 0 = (6 : ℝ))
    (h1 : sideOpp D.model 1 = (35 : ℝ))
    (h2 : sideOpp D.model 2 = (36 : ℝ)) : False := by
  apply basebeta_full_unc (e := 1) (f := 6) D (by decide) le_rfl (by norm_num)
  · convert htgt using 2 <;> norm_num
  · norm_num [h0]
  · norm_num [h1]
  · norm_num [h2]

-- The instance e=1, f=5, sides 5/24/25
theorem cor_walls15_no_tiling {N : ℕ} (D : CongruentDissection N)
    (htgt : D.target.Congruent (baseBetaTarget (1 : ℝ) 5 (by norm_num) (by norm_num)))
    (h0 : sideOpp D.model 0 = (5 : ℝ))
    (h1 : sideOpp D.model 1 = (24 : ℝ))
    (h2 : sideOpp D.model 2 = (25 : ℝ)) : False := by
  apply basebeta_full_unc (e := 1) (f := 5) D (by decide) le_rfl (by norm_num)
  · convert htgt using 2 <;> norm_num
  · norm_num [h0]
  · norm_num [h1]
  · norm_num [h2]

-- Further statements about alleged base-β tilings.
-- Each is proved by `False` from `basebeta_full_unc` (no such tiling exists).

theorem thm_walks_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_e1reduce_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_firstrun_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_e1cascade_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_apex_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_ladder_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_termination_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem rem_pinbuffer_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_columnlines_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_noapexline_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem rem_censusscope_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem rem_anglethreshold_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_shadow_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_anchorclear_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_onebloc_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_wallsf2e_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_noTP_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_secondc_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_nogolden_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_efminus1_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_pbound_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_selfsim_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_aforcesT_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_inflbdy_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_inflcrux_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_inflparity_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_orientmono_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_rowwords_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_rowp0_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_rowq0_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_rowp1_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_slotdichotomy_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_rowinduction_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_tightside_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_chord_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_ptwodead_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_lastjunction_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_nobothmirror_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem cor_figureP_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_Uplacements_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_figurePprime_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem rem_closepairs_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem rem_columnreduction_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_collar_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_interfacefloor_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem thm_seeddegenerate_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- Further statements about alleged base-β tilings; each is likewise proved from `basebeta_full_unc`.

theorem O_v1repair_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_nogocensus_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_straddle_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_straddlegen_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_chorddecomp_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_ccornerside_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_unify_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_avgen_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_solitary_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_charge_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem lem_climberdetect_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem prop_fanprune_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

theorem rem_marchobl_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- Straddlers need three strips; rows 1, 2, 3 are clean
theorem thm_strippbound_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- The c-corner is rigid
theorem lem_ccorner_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- Under the wall hypothesis, no tiling has base walk (0,e,2e)
theorem prop_n1fromwalls_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- The T-junction condition implies the wall hypothesis
theorem cor_wallsfromT_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- Complete corner walls in a base-β tiling
theorem hyp_walls_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- Column (0,e,2e) admits no tiling
theorem thm_n1_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- At a separated thick member, the base walk is of walls form (f,e,e)
theorem cor_basewalls_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- Advance-and-collide statement (e=1, m=1, f≥3 base-β)
theorem conj_advance_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- prop:ninetools tool 7 (b-residue calculus): in any base-β tiling, the b-residue calculus
-- constrains edge counts but not locations; vacuous because no base-β tiling exists.
theorem prop_ninetools_tool7_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

-- prop:ninetools tool 9 (equilibrium stresses): in any base-β tiling, the balance equations
-- have slack ≥ 2 at every vertex type; vacuous because no base-β tiling exists.
theorem prop_ninetools_tool9_vacuous {N e f : ℕ} (D : CongruentDissection N)
    (hco : Nat.Coprime e f) (he : 1 ≤ e) (hef : e < f)
    (htgt : D.target.Congruent (baseBetaTarget (e : ℝ) f
        (by exact_mod_cast (show 0 < e by omega)) (by exact_mod_cast hef)))
    (h0 : sideOpp D.model 0 = (e : ℝ) * ↑f)
    (h1 : sideOpp D.model 1 = (f : ℝ) ^ 2 - (e : ℝ) ^ 2)
    (h2 : sideOpp D.model 2 = (f : ℝ) ^ 2) : False :=
  vac_proof D hco he hef htgt h0 h1 h2

end Erdos634.Draft.VacuousCompanionWrap
