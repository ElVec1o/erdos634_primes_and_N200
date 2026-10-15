import Erdos634.BaseBetaTargetCoord

/-!
# Explicit base-β target triangle: wrapper

Re-exports results of `BaseBetaTargetCoord`:
- `cornerAngle_base₀/₁`: the two base corners of `baseBetaTarget e f` carry angle `modelBeta`
- `cornerAngle_apex`: the apex carries `3 * modelAlpha`
- `baseBetaTarget_htarget`: all corners are labeled correctly (discharged `htarget`)
- `modelBeta_mem`: `modelBeta e f ∈ (0, π)`
- Witness: `baseBetaTarget 1 2 (by norm_num) (by norm_num)` exists

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.BaseBetaTargetCoordWrap

open Erdos634.BaseBetaTargetCoord Erdos634.Geometry

theorem bbtc_cornerAngle_base₀ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    cornerAngle ((baseBetaTarget e f he hef).pts 1) ((baseBetaTarget e f he hef).pts 0)
      ((baseBetaTarget e f he hef).pts 2) = modelBeta e f :=
  cornerAngle_base₀ he hef

theorem bbtc_cornerAngle_base₁ {e f : ℝ} (he : 0 < e) (hef : e < f) :
    cornerAngle ((baseBetaTarget e f he hef).pts 2) ((baseBetaTarget e f he hef).pts 1)
      ((baseBetaTarget e f he hef).pts 0) = modelBeta e f :=
  cornerAngle_base₁ he hef

theorem bbtc_cornerAngle_apex {e f : ℝ} (he : 0 < e) (hef : e < f) :
    cornerAngle ((baseBetaTarget e f he hef).pts 0) ((baseBetaTarget e f he hef).pts 2)
      ((baseBetaTarget e f he hef).pts 1) = 3 * modelAlpha e f :=
  cornerAngle_apex he hef

theorem bbtc_htarget {e f : ℝ} (he : 0 < e) (hef : e < f) :
    ∀ k : Fin 3,
      cornerAngle ((baseBetaTarget e f he hef).pts (k + 1)) ((baseBetaTarget e f he hef).pts k)
        ((baseBetaTarget e f he hef).pts (k + 2)) = 3 * modelAlpha e f ∨
      cornerAngle ((baseBetaTarget e f he hef).pts (k + 1)) ((baseBetaTarget e f he hef).pts k)
        ((baseBetaTarget e f he hef).pts (k + 2)) = modelBeta e f :=
  baseBetaTarget_htarget he hef

theorem bbtc_modelBeta_mem {e f : ℝ} (he : 0 < e) (hef : e < f) :
    0 < modelBeta e f ∧ modelBeta e f < Real.pi / 2 :=
  modelBeta_mem he hef

-- Non-vacuity: e=1, f=2 gives he : 0 < 1 and hef : 1 < 2
example : 0 < modelBeta 1 2 ∧ modelBeta 1 2 < Real.pi / 2 :=
  bbtc_modelBeta_mem (by norm_num) (by norm_num)

#print axioms bbtc_cornerAngle_base₀
#print axioms bbtc_htarget
#print axioms bbtc_modelBeta_mem

end Erdos634.Draft.BaseBetaTargetCoordWrap
