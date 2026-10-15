import Erdos634.MirrorKill

/-!
# Isosceles mirror reduces Route 1: wrapper

The isosceles mirror sends every route-1 word `aⁱ c aʲ b a^{k'}`
to its reversal `a^{k'} b aʲ c aⁱ`, which is in the cascade's domain (b preceded only
by a-letters). Hence route-1 tilings all reduce to the cascade.

Key combinatorial facts in `MirrorKill.lean`:

1. **`k_ge_two`**: k' ≥ 2 automatically (from b-position constraint).
2. **`rev_b_position`**: 3 ≤ k'+1 ≤ f−1 (reversed word admissible).
3. **`revLetters_eq`**: W^R = a^{k'} b aʲ c aⁱ (computed, not asserted).
4. **`rev_prefix_all_a`**: first k' letters of W^R are all 'a'.
5. **`rev_b_index`**: the b of W^R is at index k'.
6. **`rev_no_c_before_b`**: no 'c' in the k'-prefix.
7. **`mirror_reduces_route1`**: cascade_kills + mirror ⟹ no route-1 tiling.

`cascade_kills` (a base word whose b is preceded only by a-letters admits no tiling) is a hypothesis of the
reduction, not proved in this file for general f.

No sorry; seven combinatorial facts; standard axioms.
-/

namespace Erdos634.Draft.MirrorKillWrap

open Erdos634.MirrorKill

/-- k' ≥ 2 is automatic from the b-position constraint. -/
theorem mirrorkill_k_ge_two {f : ℕ} (w : Word f) : 2 ≤ w.k :=
  k_ge_two w

/-- The reversed word's b is admissible: 3 ≤ k'+1 ≤ f−1. -/
theorem mirrorkill_rev_admissible {f : ℕ} (w : Word f) : 3 ≤ w.k + 1 ∧ w.k + 1 ≤ f - 1 :=
  rev_b_position w

/-- W^R = a^{k'} b aʲ c aⁱ (computed). -/
theorem mirrorkill_rev_form {f : ℕ} (w : Word f) :
    revLetters w =
      List.replicate w.k 'a' ++ ['b'] ++ List.replicate w.j 'a' ++ ['c'] ++
        List.replicate w.i 'a' :=
  revLetters_eq w

/-- The k'-prefix of W^R consists only of 'a'-letters. -/
theorem mirrorkill_prefix_all_a {f : ℕ} (w : Word f) :
    (revLetters w).take w.k = List.replicate w.k 'a' :=
  rev_prefix_all_a w

/-- The b of W^R sits at index k'. -/
theorem mirrorkill_b_at_index {f : ℕ} (w : Word f) :
    (revLetters w)[w.k]? = some 'b' :=
  rev_b_index w

/-- No 'c' in the prefix before b of W^R. -/
theorem mirrorkill_no_c_before_b {f : ℕ} (w : Word f) :
    'c' ∉ (revLetters w).take w.k :=
  rev_no_c_before_b w

/-- The reduction: cascade kills all route-1 words (given cascade_kills as hypothesis). -/
theorem mirrorkill_reduction {f : ℕ} (w : Word f)
    (tiles : Word f → Prop) (cascadeWord : ℕ → Prop)
    (mirror : ∀ v : Word f, tiles v → cascadeWord v.k)
    (cascade_kills : ∀ pre : ℕ, 2 ≤ pre → ¬ cascadeWord pre) :
    ¬ tiles w :=
  mirror_reduces_route1 w tiles cascadeWord mirror cascade_kills

/-- Non-vacuity: the f=4 word (i,j,k)=(1,1,2) exists. -/
theorem mirrorkill_f4_witness : ∃ w : Word 4, w.i = 1 ∧ w.j = 1 ∧ w.k = 2 :=
  f_four_witness

#print axioms mirrorkill_k_ge_two
#print axioms mirrorkill_rev_admissible
#print axioms mirrorkill_rev_form
#print axioms mirrorkill_reduction
#print axioms mirrorkill_f4_witness

end Erdos634.Draft.MirrorKillWrap
