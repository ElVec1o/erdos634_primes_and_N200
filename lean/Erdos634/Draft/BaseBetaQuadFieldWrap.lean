import Erdos634.BaseBetaQuadField

namespace Erdos634.Draft.BaseBetaQuadFieldWrap

open Erdos634.BaseBetaQuad Complex

theorem bbqf_sD_sq (e f : ℚ) (h : 0 ≤ Dq e f) : sD e f ^ 2 = -((Dq e f : ℚ) : ℂ) :=
  sD_sq e f h

theorem bbqf_emb_qmul (e f : ℚ) (h : 0 ≤ Dq e f) (z w : ℚ × ℚ) :
    emb e f (qmul e f z w) = emb e f z * emb e f w :=
  emb_qmul e f h z w

theorem bbqf_V_mul (e f : ℚ) (h : 0 ≤ Dq e f) {u v : ℂ} (hu : u ∈ V e f) (hv : v ∈ V e f) :
    u * v ∈ V e f :=
  V_mul e f h hu hv

theorem bbqf_V_add (e f : ℚ) {u v : ℂ} (hu : u ∈ V e f) (hv : v ∈ V e f) : u + v ∈ V e f :=
  V_add e f hu hv

theorem bbqf_V_one (e f : ℚ) : (1 : ℂ) ∈ V e f := V_one e f

example : bbqf_V_one 1 1 = V_one 1 1 := rfl

#print axioms bbqf_emb_qmul

end Erdos634.Draft.BaseBetaQuadFieldWrap
