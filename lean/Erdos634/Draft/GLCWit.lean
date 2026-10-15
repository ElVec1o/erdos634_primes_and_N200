import Mathlib.Tactic
import Erdos634.Draft.GLCCorner
import Erdos634.Draft.G3GControl

/-!
# Witnesses and counterexample checks on the real 1125-tiling (`k = 2`, tile `(4,5,6)·16`)

`witness_corner_G1`: `GLCCorner.corner_far_reflection_2a` on `G3GControl.D` (`CongruentDissection 1125`, certified by `G3GCert`, model `TwoAlphaData α 64 80 96`,
target the isosceles triangle with base angles `α`) at the target corner `0`; the word lemma for `a = 64` is `GLCArith.hword_a_real` at `k = 2`, `s = 16`.
Counterexample checks: `ctl_apex` (the apex corner, angle `π − 2α ≠ α`, is NOT an `α`-corner: the hypothesis `hk` is doing work) and
`ctl_word_wrong_k` (the word lemma `GLCArith.word_a` is false for the non-tile-shaped triple `(k²,2k+1,k(k+1))` at `k = 1`).
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Draft.G3GControl Erdos634.Draft.G3CAng
open Erdos634.Draft.G3GTiling1125 (cert cert_len)

theorem hword_1125 : ∀ x y z : ℕ, (x : ℝ) * 64 + y * 80 + z * 96 = 64 → x + y + z = 1 := by
  intro x y z h
  have h2 := hword_a_real 2 le_rfl (s := 16) (by norm_num) x y z (by push_cast; linarith)
  exact h2

theorem dist01 : dist (D.target.pts 0) (D.target.pts (0 + 1)) = 3600 := by
  have := t_opp2
  have e : (2 : Fin 3) + 1 = 0 := by decide
  have e' : (2 : Fin 3) + 2 = 1 := by decide
  unfold Tri.oppLen at this
  rw [e, e'] at this
  simpa using this

theorem dist02 : dist (D.target.pts 0) (D.target.pts (0 + 2)) = 2400 := by
  have := t_opp1
  have e : (1 : Fin 3) + 1 = 2 := by decide
  have e' : (1 : Fin 3) + 2 = 0 := by decide
  unfold Tri.oppLen at this
  rw [e, e', dist_comm] at this
  simpa using this

/-- **WITNESS (G1 at an `α`-corner on a real dissection).** -/
theorem witness_corner_G1 :
    ∃ (i : Fin cert.leaves.length) (j : Fin 3), (D.tile i).pts j = D.target.pts 0 ∧ (D.tile i).angleAt j = α ∧
      dist ((D.tile i).pts (j + 1)) ((D.tile i).pts (j + 2)) = 64 ∧
      ∃ j' : Fin cert.leaves.length, j' ≠ i ∧ ∃ X : Plane,
        (D.tile i).carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2), X} ∧
        (D.tile j').carrier = convexHull ℝ {(D.tile i).pts (j + 1), (D.tile i).pts (j + 2),
          (D.tile i).pts (j + 1) + (D.tile i).pts (j + 2) - X} := by
  have hs := corner_far_reflection_2a D (α := α) (a := 64) (b := 80) (c := 96) (fun h => α_irr h) data (by norm_num) (by norm_num) hword_1125 0 t_ang0
    (by rw [dist01]; norm_num) (by rw [dist01]; norm_num)
    (by rw [dist02]; norm_num) (by rw [dist02]; norm_num)
  obtain ⟨i, j, h1, h2, -, h4, h5⟩ := hs
  exact ⟨i, j, h1, h2, h4, h5⟩

/-- The apex corner is not an `α`-corner. -/
theorem ctl_apex : D.target.angleAt 2 ≠ α := by
  intro h
  have hs := sum_perm D.target 1
  simp only [Equiv.Perm.coe_one, id_eq] at hs
  rw [h, t_ang0, t_ang1] at hs
  exact α_irr ⟨1 / 3, by push_cast; linarith⟩

/-- The hypothesis `2 ≤ k` of the arithmetic is needed: at `k = 1` (degenerate tile `(1,3,2)`) `2a = 0a+0b+1c`,
so the conclusion of `word_2a` fails (`GLCArith.word_2a_fails_k1`). -/
theorem ctl_word_wrong_k : (0 : ℕ) * 1 ^ 2 + 0 * (2 * 1 + 1) + 1 * (1 * (1 + 1)) = 2 * 1 ^ 2 :=
  (word_2a_fails_k1).1

end Erdos634.GLC

#print axioms Erdos634.GLC.witness_corner_G1
#print axioms Erdos634.GLC.ctl_apex
