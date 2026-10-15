import Erdos634.E1NormalForm

/-!
# E1NormalForm: normal form reduction for e=1 dissections, wrapper

Key theorems:
- `normal_form`: reduce any `CongruentDissection` to normal position
- `congruent_modelTri_of_sides`: SSS congruence to the model tile
- `e1_family_of_word`: from normal form + base word → False

No sorry, standard axioms.
-/

namespace Erdos634.Draft.E1NormalFormWrap

open Erdos634.E1NormalForm Erdos634.Geometry Erdos634.TilePlacement
    Erdos634.MarchCompose Erdos634.BaseBetaTargetCoord

theorem e1nf_congruent_modelTri_of_sides (n : ℕ) (hn : 2 ≤ n) (T : Tri)
    (h0 : sideOpp T 0 = n) (h1 : sideOpp T 1 = (n : ℝ) ^ 2 - 1) (h2 : sideOpp T 2 = (n : ℝ) ^ 2) :
    T.Congruent (modelTri n (by exact_mod_cast (show 1 < n by omega))) :=
  congruent_modelTri_of_sides n hn T h0 h1 h2

theorem e1nf_target_self_congruent (n : ℕ) (hn : 2 ≤ n) :
    (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))).Congruent
      (baseBetaTarget 1 n one_pos (by exact_mod_cast (show 1 < n by omega))) :=
  target_self_congruent n hn

theorem e1nf_model_self_congruent (n : ℕ) (hn : 2 ≤ n) :
    (modelTri n (by exact_mod_cast (show 1 < n by omega))).Congruent
      (modelTri n (by exact_mod_cast (show 1 < n by omega))) :=
  model_self_congruent n hn

#print axioms e1nf_congruent_modelTri_of_sides
#print axioms e1nf_target_self_congruent
#print axioms e1nf_model_self_congruent

end Erdos634.Draft.E1NormalFormWrap
