import Erdos634.MarchCompose

/-!
# MarchCompose — word elimination + modelTri definition: wrapper

Key results:
- `modelTri_sides`: sides of `modelTri f` are `(f, f²−1, f²)` in `sideOpp` order
- `modelTri_angles`: corner angles of `modelTri f` are `(α, β, 2α+β)`
- `base_word_dies`: both base word families eliminated (wrapped via `mc_base_word_dies`)
- `bundle_witness`: for every `n ≥ 2`, the (f,f²−1,f²) tile exists with model angles

No sorry; standard axioms.
-/

namespace Erdos634.Draft.MarchComposeWrap

open Erdos634.MarchCompose Erdos634.Geometry Erdos634.TilePlacement
    Erdos634.BaseBetaTargetCoord Erdos634.MarchSlots Erdos634.MarchKillsFan

theorem mc_modelTri_sides {f : ℝ} (hf : 2 ≤ f) :
    sideOpp (modelTri f (by linarith)) 0 = f ∧
    sideOpp (modelTri f (by linarith)) 1 = f ^ 2 - 1 ∧
    sideOpp (modelTri f (by linarith)) 2 = f ^ 2 :=
  modelTri_sides hf

theorem mc_modelTri_angles {f : ℝ} (hf : 2 ≤ f) :
    cornerAngle ((modelTri f (by linarith)).pts 1) ((modelTri f (by linarith)).pts 0)
        ((modelTri f (by linarith)).pts 2) = modelAlpha 1 f ∧
    cornerAngle ((modelTri f (by linarith)).pts 2) ((modelTri f (by linarith)).pts 1)
        ((modelTri f (by linarith)).pts 0) = modelBeta 1 f ∧
    cornerAngle ((modelTri f (by linarith)).pts 0) ((modelTri f (by linarith)).pts 2)
        ((modelTri f (by linarith)).pts 1) = 2 * modelAlpha 1 f + modelBeta 1 f :=
  modelTri_angles hf

theorem mc_base_word_dies {N : ℕ} (D : CongruentDissection N) {f α β γ : ℝ} (hf : 2 ≤ f)
    {n : ℕ} (hn : (n : ℝ) = f) (hn3 : 3 ≤ n)
    (htgt : D.target = baseBetaTarget 1 f one_pos (by linarith))
    (hM : ModelData D f α β γ) (hA : AngleData α β γ)
    {p q r : ℕ} (hp : 1 ≤ p) (hr : 1 ≤ r) (hpqr : p + q + r = n)
    (hw : LaysWordBFirst D f p q r ∨ LaysWordCFirst D f p q r) : False :=
  base_word_dies D hf hn hn3 htgt hM hA hp hr hpqr hw

-- Non-vacuity witness for mc_modelTri_sides
example : sideOpp (modelTri 2 (by norm_num)) 0 = 2 :=
  (mc_modelTri_sides (by norm_num : (2:ℝ) ≤ 2)).1

#print axioms mc_modelTri_sides
#print axioms mc_modelTri_angles
#print axioms mc_base_word_dies

end Erdos634.Draft.MarchComposeWrap
