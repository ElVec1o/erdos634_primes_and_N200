import Mathlib.Tactic
import Erdos634.Draft.GLCG2

/-!
# `corner_G2_k`: G2 for the tile `(k², 2k+1, k(k+1))·s`, `k ≥ 2`

`corner_G2` with the arithmetic side conditions (`a ≠ b, a ≠ c, b ≠ c, b < c`, the edge lengths of the model, the word lemmas for `a`, `2a`, `c`) discharged from `GLCArith`/`GLCArith2` for the tile `(a,b,c) = (s k², s(2k+1), s k(k+1))`,
`k ≥ 2`, `s > 0`.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.C2Forward Erdos634.Pi3F6 Erdos634.Pi3Tile Erdos634.EdgeWordConversion

variable {N : ℕ}

set_option maxHeartbeats 3200000 in
theorem corner_G2_k (D : CongruentDissection N) {α a b c s : ℝ} (k : ℕ) (hk2 : 2 ≤ k) (hs : 0 < s)
    (ha : a = s * (k : ℝ) ^ 2) (hb : b = s * (2 * k + 1)) (hc : c = s * (k * (k + 1)))
    (hα : ¬ ∃ r : ℚ, α = (r : ℝ) * Real.pi) (hS : D.model.TwoAlphaData α a b c)
        (k0 : Fin 3) (hk : D.target.angleAt k0 = α)
    (hA1 : dist (D.target.pts k0) (D.target.pts (k0 + 1)) ≠ b)
    (hA2 : dist (D.target.pts k0) (D.target.pts (k0 + 1)) ≠ c)
    (hB1 : dist (D.target.pts k0) (D.target.pts (k0 + 2)) ≠ b)
    (hB2 : dist (D.target.pts k0) (D.target.pts (k0 + 2)) ≠ c) :
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
                ((D.tile K').pts (l'' + 2) - ((D.tile i).pts m1 + ((D.tile i).pts m1 - D.target.pts k0)))) := by
  have hk0 : (2 : ℝ) ≤ k := by exact_mod_cast hk2
  have hkk : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
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
  have hbc : b ≠ c := by
    rw [hb, hc]; intro h
    have h' : 2 * (k : ℝ) + 1 = k * (k + 1) := mul_left_cancel₀ hs.ne' h
    have h3 : (k : ℝ) < 3 := by nlinarith
    have hk3 : k < 3 := by exact_mod_cast h3
    interval_cases k
    norm_num at h'
  have hbc' : b < c := by
    rw [hb, hc]; exact mul_lt_mul_of_pos_left (by nlinarith) hs
  have hb0 : 0 < b := by rw [hb]; positivity
  have hsides := sideLen_mem_2a D hS
  have hword : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x + y + z = 1 := by
    intro x y z h
    rw [ha, hb, hc] at h
    exact hword_a_real k hk2 hs x y z h
  have hword1 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = a → x = 1 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    rw [ha, hb, hc] at h
    exact hword_a_full k hk2 hs x y z h
  have hword2 : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = 2 * a → x = 2 ∧ y = 0 ∧ z = 0 := by
    intro x y z h
    rw [ha, hb, hc] at h
    exact hword_2a_real k hk2 hs x y z h
  have hwordc : ∀ x y z : ℕ, (x : ℝ) * a + y * b + z * c = c → x = 0 ∧ y = 0 ∧ z = 1 := by
    intro x y z h
    rw [ha, hb, hc] at h
    exact hword_c_real k hk2 hs x y z h
  exact corner_G2 D hα hS hab hac hbc hb0 hbc' hsides hword hword1 hword2 hwordc k0 hk hA1 hA2 hB1 hB2

end Erdos634.GLC

#print axioms Erdos634.GLC.corner_G2_k
