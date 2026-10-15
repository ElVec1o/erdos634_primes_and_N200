import Mathlib.Tactic
import Erdos634.Draft.T30LPi3F6Corner
import Erdos634.Draft.T30LPi3L3

/-!
# `corner_far_reflection` for the tile `(9+√21, 9−√21, 12)` in an equilateral target of side 60

The hypotheses are about an arbitrary `CongruentDissection` whose model has `SixtyData α sa sb sc` and `α ∉ ℚπ`; no such dissection is
claimed to exist. The word lemma is `ChordWord.chord_c`; the side lengths `60 ∉ {sa, sb}` are proved.
-/

namespace Erdos634.Pi3F6

open Erdos634.Geometry Erdos634.Pi3Tile Erdos634.ChordWord

theorem sa_ne_sc : sa ≠ sc := Ne.symm Erdos634.Pi3L3.sc_ne_sa
theorem sb_ne_sc : sb ≠ sc := Ne.symm Erdos634.Pi3L3.sc_ne_sb

theorem sixty_ne_sa : (60 : ℝ) ≠ sa := by
  intro h
  have h21 : Real.sqrt 21 < 5 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  unfold sa at h; linarith

theorem sixty_ne_sb : (60 : ℝ) ≠ sb := by
  intro h
  have h21 : 0 ≤ Real.sqrt 21 := Real.sqrt_nonneg _
  unfold sb at h; linarith

theorem t30_corner_far_reflection {N : ℕ} (D : CongruentDissection N) {α : ℝ} (hirr : Irr α)
    (hS : D.model.SixtyData α sa sb sc) (k : Fin 3) (hk : D.target.angleAt k = Real.pi / 3)
    (h1 : dist (D.target.pts k) (D.target.pts (k + 1)) = 60)
    (h2 : dist (D.target.pts k) (D.target.pts (k + 2)) = 60) :
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k ∧
      ∃ j' : Fin N, j' ≠ i ∧ ∃ X : Plane,
        (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
        (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
          (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} :=
  corner_far_reflection D hirr hS sa_ne_sc sb_ne_sc
    (fun x y z h => by
      have := chord_c x y z (by unfold wordLen; exact h)
      omega)
    k hk (by rw [h1]; exact sixty_ne_sa) (by rw [h1]; exact sixty_ne_sb)
    (by rw [h2]; exact sixty_ne_sa) (by rw [h2]; exact sixty_ne_sb)

end Erdos634.Pi3F6

#print axioms Erdos634.Pi3F6.t30_corner_far_reflection
