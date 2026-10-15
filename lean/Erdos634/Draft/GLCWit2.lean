import Mathlib.Tactic
import Erdos634.Draft.GLCT4Wire
import Erdos634.Draft.GLCWit

/-!
# Witness for `corner_G1` and `corner_G1_T4` on the real 1125-tiling

Every hypothesis of `GLCG1.corner_G1` and `GLCT4Wire.corner_G1_T4` is discharged on `G3GControl.D` (`CongruentDissection 1125`, tile `(4,5,6)·16`, `k = 2`) at the target corner `0`
(angle `α`): `α ∉ ℚπ`, `TwoAlphaData α 64 80 96`, the word lemma for `a` (`GLCArith.hword_a_real`), the side lengths `3600, 2400 ∉ {80, 96}`.
Scope: the conclusions are instantiated (existence of `K_Q` with `α` at `Q` and the `T4Concl` implications); the antecedent of the `T4Concl` implications
(the edge of `K_Q` along the side has length `|OQ|`, the "(c,c)" configuration) is not machine-checked on this tiling (that needs the identity of the tile `K_Q` in the certificate);
it is checked on the exact coordinates of the tiling (at every `α` corner the side reads `c,c,c`), not in Lean.
-/

namespace Erdos634.GLC

open Erdos634.Geometry Erdos634.Draft.G3GControl Erdos634.Draft.G3CAng
open Erdos634.Draft.G3GTiling1125 (cert cert_len)

theorem witness_corner_G1_full :
    ∃ (i : Fin cert.leaves.length) (j : Fin 3), (D.tile i).pts j = D.target.pts 0 ∧ (D.tile i).angleAt j = α ∧
      (∃ (K : Fin cert.leaves.length) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 1) ∧ (D.tile K).angleAt l = α ∧
        T4Concl D i j (j + 1) (j + 2) K l) ∧
      (∃ (K : Fin cert.leaves.length) (l : Fin 3), (D.tile K).pts l = (D.tile i).pts (j + 2) ∧ (D.tile K).angleAt l = α ∧
        T4Concl D i j (j + 2) (j + 1) K l) := by
  obtain ⟨i, j, h1, h2, ⟨KQ, lQ, a1, a2, -, a3⟩, ⟨KP, lP, b1, b2, -, b3⟩⟩ :=
    corner_G1_T4 D (α := α) (a := 64) (b := 80) (c := 96) (fun h => α_irr h) data (by norm_num) (by norm_num)
      hword_1125 0 t_ang0 (by rw [dist01]; norm_num) (by rw [dist01]; norm_num)
      (by rw [dist02]; norm_num) (by rw [dist02]; norm_num)
  exact ⟨i, j, h1, h2, ⟨KP, lP, b1, b2, b3⟩, ⟨KQ, lQ, a1, a2, a3⟩⟩

end Erdos634.GLC

#print axioms Erdos634.GLC.witness_corner_G1_full
