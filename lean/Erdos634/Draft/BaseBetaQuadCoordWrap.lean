import Erdos634.BaseBetaQuadCoord

namespace Erdos634.Draft.BaseBetaQuadCoordWrap

open Erdos634.BaseBetaQuad

theorem bbqc_qmul_comm (e f : ℚ) (z w : ℚ × ℚ) : qmul e f z w = qmul e f w z :=
  qmul_comm e f z w

theorem bbqc_qmul_assoc (e f : ℚ) (z w v : ℚ × ℚ) :
    qmul e f (qmul e f z w) v = qmul e f z (qmul e f w v) :=
  qmul_assoc e f z w v

theorem bbqc_zetaQ_norm_one (e f : ℚ) (hf : f ≠ 0) :
    qmul e f (zetaQ e f) (qconj (zetaQ e f)) = (1, 0) :=
  zetaQ_norm_one e f hf

theorem bbqc_xiQ_norm_one (e f : ℚ) (hf : f ≠ 0) :
    qmul e f (xiQ e f) (qconj (xiQ e f)) = (1, 0) :=
  xiQ_norm_one e f hf

theorem bbqc_xiQ_sq_zetaQ_cube (e f : ℚ) (hf : f ≠ 0) :
    qmul e f (qmul e f (xiQ e f) (xiQ e f))
      (qmul e f (zetaQ e f) (qmul e f (zetaQ e f) (zetaQ e f))) = (-1, 0) :=
  xiQ_sq_zetaQ_cube e f hf

example : bbqc_qmul_comm 1 1 (1, 0) (0, 1) = qmul_comm 1 1 (1, 0) (0, 1) := rfl

#print axioms bbqc_xiQ_sq_zetaQ_cube

end Erdos634.Draft.BaseBetaQuadCoordWrap
