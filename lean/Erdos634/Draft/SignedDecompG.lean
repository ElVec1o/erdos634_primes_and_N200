/-
Draft/SignedDecompG.lean  In `AllThreshold`.

Paper: Proposition `prop:layerall`, part (a), for every member `(e, f)` (coprimality is not used: the statement is the
identity `b + e^2 = c` and the frame of `SignedDecompE1`).

`SignedDecompE1.signed_decomposition_real` proves the signed decomposition for REAL parameters `F > 1`, `t > 0`: the
big triangle `ABC` has the sides `t F^3`, `t F^3`, `t (3 F^2 - 1)`; `Q'QZ` has `t F`, `t F^2`, `t (F^2 - 1)`; and `ABQ'`,
`AQ'Z`, `ACQ` have `t F F`, `t F F^2`, `t F (F^2 - 1)`.  For the member `(e, f)` at the scale `M` put `F = f / e` and
`t = M e^3`.  Then (identities used, all by `field_simp; ring`, with `b = f^2 - e^2`)

    t F^3        = M f^3                    t (3 F^2 - 1) = M e (3 f^2 - e^2)
    t F          = (M e) (e f)              t F^2         = (M e) f^2              t (F^2 - 1) = (M e) b
    t F F        = (f M) (e f)              t F F^2       = (f M) f^2              t F (F^2 - 1) = (f M) b

so `Q'QZ` is the tile `(a, b, c) = (e f, f^2 - e^2, f^2)` at scale `M e` and `ABQ'`, `AQ'Z`, `ACQ` are the tile at scale
`f M`, with the sides listed in the order `(a, c, b)` of `SignedDecompE1`.

What is NOT in this file: the sentence of the paper "the triangle `ABQ` is a copy of `W_M(e, f)` and
`ABQ ∪ Q'QZ = ABQ' ∪ AQ'Z`" (the `W` half of part (a)); `SignedDecompE1` proves only the `T_M` half, and so does this file.

No sorry, no native_decide.  `#print axioms` at the foot.
-/
import Erdos634.Draft.SignedDecompE1

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Erdos634.Draft.SignedDecompG
open Erdos634.Draft.SignedDecompE1
open Erdos634.Draft.FDBBaseBetaE1 (HasSides)

/-- `F = f / e > 1` for `1 ≤ e < f` -/
theorem member_F_gt {e f : ℕ} (he : 1 ≤ e) (hef : e < f) : 1 < (f : ℝ) / (e : ℝ) := by
  have he0 : (0 : ℝ) < e := natpos he
  rw [one_lt_div he0]
  exact_mod_cast hef

/-- `t = M e^3 > 0` for `1 ≤ e`, `1 ≤ M` -/
theorem member_t_pos {e M : ℕ} (he : 1 ≤ e) (hM : 1 ≤ M) : (0 : ℝ) < (M : ℝ) * (e : ℝ) ^ 3 :=
  mul_pos (natpos hM) (pow_pos (natpos he) 3)

/-- the natural number `f^2 - e^2` (`e < f`) is the real `f^2 - e^2` -/
theorem cast_sub_sq {e f : ℕ} (hef : e < f) :
    ((f ^ 2 - e ^ 2 : ℕ) : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  rw [Nat.cast_sub (Nat.pow_le_pow_left hef.le 2), Nat.cast_pow, Nat.cast_pow]

/-- the natural number `3 f^2 - e^2` (`e < f`) is the real `3 f^2 - e^2` -/
theorem cast_sub_sq3 {e f : ℕ} (hef : e < f) :
    ((3 * f ^ 2 - e ^ 2 : ℕ) : ℝ) = 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 := by
  have h : e ^ 2 ≤ 3 * f ^ 2 := by
    have := Nat.pow_le_pow_left hef.le 2
    omega
  rw [Nat.cast_sub h]
  push_cast
  try ring

/-- **The signed decomposition of the member `(e, f)` at the scale `M`** (paper, Proposition `prop:layerall`(a), which reads:
"Let `Q', Q` be the points of the base with `|BQ'| = |CQ| = M e f^2`, and let `Z` be the point of the ray `AQ` beyond `Q` with
`|QZ| = M e a = M e^2 f`.  Then `ABQ'`, `ACQ` and `AQ'Z` are copies of the tile at scale `f M`; `Q'QZ` is a copy of the tile at
scale `M e`, lying on the other side of the base; and `T_M ∪ Q'QZ = ABQ' ∪ AQ'Z ∪ ACQ`, with disjoint interiors on each
side.  ...  So `T_M(e, f)` together with one copy of the tile at scale `M e` is three copies of the tile at scale `f M`.")

Formal content, for `F = f / e` and `t = M e^3` in the frame `Phi F` of `SignedDecompE1`: the union identity of the carriers,
the four disjointness statements (all inside `SignedDecomp`), and the side lengths in natural-number form: `ABC` has
`M f^3`, `M f^3`, `M e (3 f^2 - e^2)`; `Q'QZ` has `(M e) a`, `(M e) c`, `(M e) b`; `ABQ'`, `AQ'Z`, `ACQ` each have
`(f M) a`, `(f M) c`, `(f M) b`, where `(a, b, c) = (e f, f^2 - e^2, f^2)`.  The statement is unconditional (for
`1 ≤ e < f`, `1 ≤ M`). -/
theorem signed_decomposition_member (e f M : ℕ) (he : 1 ≤ e) (hef : e < f) (hM : 1 ≤ M) :
    SignedDecomp ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM) ∧
    HasSides (triABC ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((M * f ^ 3 : ℕ) : ℝ) ((M * f ^ 3 : ℕ) : ℝ) ((M * e * (3 * f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
    HasSides (triQ1QZ ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((M * e * (e * f) : ℕ) : ℝ) ((M * e * f ^ 2 : ℕ) : ℝ) ((M * e * (f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
    HasSides (triABQ1 ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((f * M * (e * f) : ℕ) : ℝ) ((f * M * f ^ 2 : ℕ) : ℝ) ((f * M * (f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
    HasSides (triAQ1Z ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((f * M * (e * f) : ℕ) : ℝ) ((f * M * f ^ 2 : ℕ) : ℝ) ((f * M * (f ^ 2 - e ^ 2) : ℕ) : ℝ) ∧
    HasSides (triACQ ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3) (member_t_pos he hM))
      ((f * M * (e * f) : ℕ) : ℝ) ((f * M * f ^ 2 : ℕ) : ℝ) ((f * M * (f ^ 2 - e ^ 2) : ℕ) : ℝ) := by
  have he0 : (e : ℝ) ≠ 0 := (natpos he).ne'
  have hsd := signed_decomposition_real ((f : ℝ) / e) (member_F_gt he hef) ((M : ℝ) * (e : ℝ) ^ 3)
    (member_t_pos he hM)
  have hsd2 := hsd
  unfold SignedDecomp at hsd2
  obtain ⟨-, -, -, -, -, sABC, sQ, sABQ, sAQZ, sACQ⟩ := hsd2
  obtain ⟨b, hbN, hbR⟩ : ∃ b : ℕ, f ^ 2 - e ^ 2 = b ∧ (b : ℝ) = (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
    ⟨_, rfl, cast_sub_sq hef⟩
  obtain ⟨b3, hb3N, hb3R⟩ : ∃ b3 : ℕ, 3 * f ^ 2 - e ^ 2 = b3 ∧
      (b3 : ℝ) = 3 * (f : ℝ) ^ 2 - (e : ℝ) ^ 2 :=
    ⟨_, rfl, cast_sub_sq3 hef⟩
  rw [hbN, hb3N]
  refine ⟨hsd, ?_, ?_, ?_, ?_, ?_⟩
  · refine hasSides_eq sABC ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); (try rw [hb3R]);
       first | (field_simp; ring1) | field_simp | ring1)
  · refine hasSides_eq sQ ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); (try rw [hb3R]);
       first | (field_simp; ring1) | field_simp | ring1)
  · refine hasSides_eq sABQ ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); (try rw [hb3R]);
       first | (field_simp; ring1) | field_simp | ring1)
  · refine hasSides_eq sAQZ ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); (try rw [hb3R]);
       first | (field_simp; ring1) | field_simp | ring1)
  · refine hasSides_eq sACQ ?_ ?_ ?_ <;>
      (push_cast; (try rw [hbR]); (try rw [hb3R]);
       first | (field_simp; ring1) | field_simp | ring1)

end Erdos634.Draft.SignedDecompG

#print axioms Erdos634.Draft.SignedDecompG.member_F_gt
#print axioms Erdos634.Draft.SignedDecompG.cast_sub_sq3
#print axioms Erdos634.Draft.SignedDecompG.signed_decomposition_member
