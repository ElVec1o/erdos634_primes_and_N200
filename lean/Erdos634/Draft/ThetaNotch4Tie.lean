-- Draft/ThetaNotch4Tie.lean -- ties `ThetaNotch.AlphaTiled` to the library statement `ThetaCompose.alpha_exists` (audit note N1, 2026-11-14).  INTERNAL BUILD ONLY, UNAUDITED.
-- No sorry, no native_decide.
/-
`AlphaTiled` (ThetaNotch4Glue) was introduced as a fresh def with the same data as `ThetaCompose.alpha_exists`.  Here the library theorem is shown to give `AlphaTiled`
at its own parameters (thin row: `0 < e`, `f f = e e + b`, `e f < b`, `g >= 2`), so the two definitions are tied.  The shapes agree definitionally (`AlphaTiled` unfolds to the
same `Prop`), so the bridge is `alpha_exists ...` itself.
CREDIT: as ThetaNotch4Glue (the hub gluing: Beeson, arXiv:1206.2229 v5, Cor. 8, Fig. 25, then Paliy; Zhang, Beeson-Rosu, Laczkovich).
-/
import Erdos634.Draft.ThetaNotch4Alpha
import Erdos634.Draft.ThetaCompose

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

namespace Erdos634.Draft.ThetaNotch
noncomputable section

/-- the library's `alpha_exists` yields `AlphaTiled` at its parameters. -/
theorem alphaTiled_of_alpha_exists (e f b : ℕ) (he : 0 < e) (hb : f * f = e * e + b) (hq : e * f < b) (g : ℕ) (hg : 2 ≤ g) :
    AlphaTiled e f b g :=
  Erdos634.Draft.ThetaCompose.alpha_exists e f b he hb hq g hg

/-- converse direction on the common range is not claimed; here: the two statements are the same `Prop` (definitional unfolding). -/
example (e f b g : ℕ) :
    AlphaTiled e f b g = (∃ D : CongruentDissection (b * (b + f * f) * g * g),
      HasSides D.target ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (2 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2))
        ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2) ((g : ℝ) * ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) * (f : ℝ) ^ 2) ∧
      HasSides D.model ((e : ℝ) * f) ((f : ℝ) ^ 2 - (e : ℝ) ^ 2) ((f : ℝ) ^ 2)) := rfl

/-- witness: a thin row, (e,f,b) = (1,3,8)?  e f = 3 < 8, f f = 9 = 1 + 8, g = 2: the hypotheses of the bridge hold. -/
example : AlphaTiled 1 3 8 2 := alphaTiled_of_alpha_exists 1 3 8 (by norm_num) (by norm_num) (by norm_num) 2 (by norm_num)

#print axioms alphaTiled_of_alpha_exists

end
end Erdos634.Draft.ThetaNotch
