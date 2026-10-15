import Erdos634.E1BaseWord

/-!
# E1BaseWord: the e=1 family theorem (f ≥ 3), wrapper

`E1BaseWord.e1_family_f_ge_3_congruent` is the culmination of the e=1 march:
for any `CongruentDissection` whose target is congruent to the `m=1, e=1` base-β target
and whose model is congruent to the tile `(n, n²−1, n²)` with `n ≥ 3`, `False`.

Together with the mod-12 reduction this excludes every prime `3f²−1 ≥ 47`.

No sorry, standard axioms.
-/

namespace Erdos634.Draft.E1BaseWordWrap

open Erdos634.E1BaseWord Erdos634.Geometry Erdos634.TilePlacement
    Erdos634.MarchCompose Erdos634.BaseBetaTargetCoord

/-- `thm:e1family` for f ≥ 3: any CongruentDissection whose target is congruent
to `baseBetaTarget 1 n` and whose model is congruent to `modelTri n` produces False. -/
theorem e1family_congruent (N : ℕ) (D₀ : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (hmod : D₀.model.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega)))) :
    False :=
  e1_family_f_ge_3_congruent D₀ hn3 htgt hmod

/-- Variant from side lengths alone. -/
theorem e1family_of_sides (N : ℕ) (D₀ : CongruentDissection N) {n : ℕ} (hn3 : 3 ≤ n)
    (htgt : D₀.target.Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))))
    (h0 : sideOpp D₀.model 0 = n)
    (h1 : sideOpp D₀.model 1 = (n : ℝ) ^ 2 - 1)
    (h2 : sideOpp D₀.model 2 = (n : ℝ) ^ 2) :
    False :=
  e1_family_f_ge_3_of_sides D₀ hn3 htgt h0 h1 h2

#print axioms e1family_congruent
#print axioms e1family_of_sides

end Erdos634.Draft.E1BaseWordWrap
