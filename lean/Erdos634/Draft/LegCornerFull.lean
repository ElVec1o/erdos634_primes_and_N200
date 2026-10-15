/-
Draft/LegCornerFull.lean -- `prop:legcorner` (main paper): the leg corner lemma for `γ = 2α`, both parts in one
statement, for the tile `s (k², 2k+1, k(k+1))`, `k ≥ 2`, `s > 0`.

Hypotheses: a congruent dissection whose tile has angles `α, β, 2α` opposite `a, b, c` (`TwoAlphaData`), `α/π`
irrational, a corner `C = D.target.pts k0` of the target of angle `α`, and neither side through `C` of length `b`
or `c`.

* (G1) = `GLC.corner_G1`: the tile `T` at `C` has angle `α` there and its two edges along the two sides; its third
  edge (the corner chord) has length `a`; a second tile is the point reflection of `T` in the midpoint of the chord;
  at each end of the chord a tile has angle `α` and an edge continuing along the side.
* (G2) = `GLC.corner_G2_k`: if `|C R| = c`, `|C P| = b` for the other two vertices `R`, `P` of `T`, the points
  `2R − C` and `2P − C` are not vertices of the target, and a tile has angle `α` at `R` with a `c`-edge continuing
  along the side, then no tile has angle `2α` at `Q₁ = 2R − C` with an edge continuing along the side, and some tile
  has angle `α` at `Q₁` with an edge continuing along the side.

The three hypotheses of `corner_G1` that concern the tile alone (`a ≠ b`, `a ≠ c`, the word lemma for `a`) are
discharged here for this tile. not prime-case work.  No sorry, no native_decide.
-/
import Erdos634.Draft.GLCG1
import Erdos634.Draft.GLCG2k
import Erdos634.Draft.GLCArith

namespace Erdos634.Draft.LegCornerFull

open Erdos634.Geometry Erdos634.GLC

variable {N : ℕ}

/-- **`prop:legcorner`.** -/
theorem prop_legcorner (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ) (hk2 : 2 ≤ k) (hs : 0 < s)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
    (k0 : Fin 3) (hk : D.target.angleAt k0 = α)
    (hA1 : dist (D.target.pts k0) (D.target.pts (k0 + 1)) ≠ b)
    (hA2 : dist (D.target.pts k0) (D.target.pts (k0 + 1)) ≠ c)
    (hB1 : dist (D.target.pts k0) (D.target.pts (k0 + 2)) ≠ b)
    (hB2 : dist (D.target.pts k0) (D.target.pts (k0 + 2)) ≠ c) :
    -- (G1)
    (
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k0 ∧ (D.tile i).angleAt j = α ∧
          ((SameRay ℝ (D.target.pts (k0 + 1) - D.target.pts k0) ((D.tile i).pts (j + 1) - D.target.pts k0) ∧
            SameRay ℝ (D.target.pts (k0 + 2) - D.target.pts k0) ((D.tile i).pts (j + 2) - D.target.pts k0)) ∨
           (SameRay ℝ (D.target.pts (k0 + 2) - D.target.pts k0) ((D.tile i).pts (j + 1) - D.target.pts k0) ∧
            SameRay ℝ (D.target.pts (k0 + 1) - D.target.pts k0) ((D.tile i).pts (j + 2) - D.target.pts k0))) ∧
          dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = a ∧
          ∃ j' : Fin N, j' ≠ i ∧ ∃ X : Plane,
            (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
            (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
              (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} ∧
          (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 1) ∧ (D.tile K).angleAt l = α ∧
              (SameRay ℝ ((D.tile i).pts (j + 1) - D.target.pts k0) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 1)) ∨
               SameRay ℝ ((D.tile i).pts (j + 1) - D.target.pts k0) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 1)))) ∧
          (∃ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 2) ∧ (D.tile K).angleAt l = α ∧
              (SameRay ℝ ((D.tile i).pts (j + 2) - D.target.pts k0) ((D.tile K).pts (l + 1) - (D.tile i).pts (j + 2)) ∨
               SameRay ℝ ((D.tile i).pts (j + 2) - D.target.pts k0) ((D.tile K).pts (l + 2) - (D.tile i).pts (j + 2))))) ∧
    -- (G2)
    (
    ∃ (i : Fin N) (j : Fin 3), (D.tile i).pts j = D.target.pts k0 ∧ (D.tile i).angleAt j = α ∧
          ∀ (m1 m2 : Fin 3), ((m1 = j + 1 ∧ m2 = j + 2) ∨ (m1 = j + 2 ∧ m2 = j + 1)) →
            dist (D.target.pts k0) ((D.tile i).pts m1) = c → dist (D.target.pts k0) ((D.tile i).pts m2) = b →
            (∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0)) →
            (∀ v' : Fin 3, D.target.pts v' ≠ (D.tile i).pts m2 + ((D.tile i).pts m2 - D.target.pts k0)) →
            ∀ (K : Fin N) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts m1 → (D.tile K).angleAt l = α →
              ((SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0) ((D.tile K).pts (l + 1) - (D.tile i).pts m1) ∧
                  dist ((D.tile i).pts m1) ((D.tile K).pts (l + 1)) = c) ∨
                (SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0) ((D.tile K).pts (l + 2) - (D.tile i).pts m1) ∧
                  dist ((D.tile i).pts m1) ((D.tile K).pts (l + 2)) = c)) →
              (¬ ∃ (U : Fin N) (l' : Fin 3), (D.tile U).pts l' = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0) ∧
                (D.tile U).angleAt l' = 2 * α ∧
                (SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                    ((D.tile U).pts (l' + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0))) ∨
                 SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                    ((D.tile U).pts (l' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0))))) ∧
              ∃ (K' : Fin N) (l'' : Fin 3), (D.tile K').pts l'' = (D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0) ∧
                (D.tile K').angleAt l'' = α ∧
                (SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                    ((D.tile K').pts (l'' + 1) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0))) ∨
                 SameRay ℝ ((D.tile i).pts m1 - D.target.pts k0)
                    ((D.tile K').pts (l'' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0))))) := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hab : a ≠ b := by
    rw [ha, hb]; intro h
    have h' : (k : ℝ) ^ 2 = 2 * k + 1 := mul_left_cancel₀ hs.ne' h
    have h3 : (k : ℝ) < 3 := by nlinarith
    have hk3 : k < 3 := by exact_mod_cast h3
    interval_cases k
    norm_num at h'
  have hac : a ≠ c := by
    rw [ha, hc]; intro h
    have h' : (k : ℝ) ^ 2 = k * (k + 1) := mul_left_cancel₀ hs.ne' h
    nlinarith
  have hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1 := by
    intro x y z h
    rw [ha, hb, hc] at h
    exact hword_a_real k hk2 hs x y z h
  exact ⟨corner_G1 D hα hS hab hac hword k0 hk hA1 hA2 hB1 hB2,
    corner_G2_k D k hk2 hs ha hb hc hα hS k0 hk hA1 hA2 hB1 hB2⟩

end Erdos634.Draft.LegCornerFull

#print axioms Erdos634.Draft.LegCornerFull.prop_legcorner
