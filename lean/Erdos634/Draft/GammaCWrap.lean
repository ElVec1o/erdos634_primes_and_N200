import Erdos634.GammaC

namespace Erdos634.Draft.GammaCWrap

open Erdos634.GammaC

/-- Thin wrapper: the Γc witness identity `e·f² = f·(e·f)`. -/
theorem wrap_gammac_witness (e f : ℕ) : e * f ^ 2 = f * (e * f) :=
  gammac_witness e f

/-- Thin wrapper: `j < N` for every Γc orbit at the base-β tile. -/
theorem wrap_gammac_j_lt_N (e f : ℕ) (he : 1 ≤ e) (hef : e < f) :
    e + e ^ 2 < 3 * f ^ 2 :=
  gammac_j_lt_N e f he hef

/-- Thin wrapper: complete classification of Γc relations. -/
theorem wrap_gammac_classification (e f j u v : ℤ) (hf : 0 < f) (hcop : IsCoprime e f)
    (h : j * f ^ 2 + v * e ^ 2 = u * (e * f) + v * f ^ 2) :
    ∃ w s : ℤ, v = f * w ∧ u = w * e + f * s ∧ j = s * e + w * f :=
  gammac_classification e f j u v hf hcop h

-- Non-vacuity: at (e,f) = (1,2), j=0, u=0, v=0 is a solution with w=s=0.
example : gammac_classification 1 2 0 0 0 (by norm_num) (by norm_num) (by ring) =
    gammac_classification 1 2 0 0 0 (by norm_num) (by norm_num) (by ring) := rfl

#print axioms wrap_gammac_classification

end Erdos634.Draft.GammaCWrap
