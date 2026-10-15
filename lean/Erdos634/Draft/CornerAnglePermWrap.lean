import Erdos634.CornerAnglePerm

/-!
# CornerAnglePerm: uniform permutation wrapper
Key results:
- `cornerAngle_perm_X`: congruence yields one permutation matching all three corner angles.
- `congruentDissection_corner_total_X`: each of the three model angles appears exactly `N` times across all tiles.
No sorry, standard axioms.
-/

namespace Erdos634.Draft.CornerAnglePermWrap
open Erdos634.Geometry

/-- Wrap: a congruence `T.Congruent U` produces a single permutation matching every corner angle. -/
theorem cornerAngle_perm_X {T U : Tri} (h : T.Congruent U) :
    ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3,
      cornerAngle (U.pts (σ k + 1)) (U.pts (σ k)) (U.pts (σ k + 2))
        = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) :=
  h.cornerAngle_perm

/-- Wrap: in a congruent dissection with pairwise distinct model angles, each angle appears exactly
`N` times across all `N` tiles. -/
theorem congruentDissection_corner_total_X {N : ℕ} (D : CongruentDissection N)
    (hdist : ∀ k l : Fin 3,
      cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))
        = cornerAngle (D.model.pts (l + 1)) (D.model.pts l) (D.model.pts (l + 2)) → k = l)
    (k : Fin 3) :
    ∑ i : Fin N, ({j | cornerAngle ((D.tile i).pts (j + 1)) ((D.tile i).pts j)
          ((D.tile i).pts (j + 2))
        = cornerAngle (D.model.pts (k + 1)) (D.model.pts k) (D.model.pts (k + 2))}
        : Finset (Fin 3)).card = N :=
  congruentDissection_corner_total D hdist k

-- Non-vacuity: cornerAngle_perm fires on the self-congruence
example (T : Tri) : ∃ σ : Equiv.Perm (Fin 3), ∀ k : Fin 3,
    cornerAngle (T.pts (σ k + 1)) (T.pts (σ k)) (T.pts (σ k + 2))
      = cornerAngle (T.pts (k + 1)) (T.pts k) (T.pts (k + 2)) :=
  cornerAngle_perm_X (Tri.Congruent.refl T)

#print axioms cornerAngle_perm_X
#print axioms congruentDissection_corner_total_X
end Erdos634.Draft.CornerAnglePermWrap
