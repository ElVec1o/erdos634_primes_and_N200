import Erdos634.ScaleRigidity

/-!
# ScaleRigidity — scale-sensitivity no-go and instance data: wrapper

Key results:
- `no_similarity_invariant_proof`: no scale-invariant criterion can certify non-tileability
- `target_similar`: e=1 f=2 family targets are similar (m-fold enlargements)
- `targets_concrete`: named target dimensions
- `counts_concrete`: tile counts 11, 44, 99
- `side_no_b_m1`: m=1 side admits only Q=0 walks
- `side_b_exists_m2/m3`: m=2,3 admit Q≠0 walks (scale-sensitivity evidence)

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.ScaleRigidityWrap

open Erdos634.ScaleRigidity

theorem sr_no_similarity_invariant_proof
    {Tile Target Data Scale : Type}
    (Tileable : Tile → Target → Prop)
    (scale : Scale → Target → Target)
    (data : Tile → Target → Data)
    (hdata : ∀ (k : Scale) (T : Tile) (S : Target), data T (scale k S) = data T S)
    (P : Data → Prop)
    (hsound : ∀ (T : Tile) (S : Target), P (data T S) → ¬ Tileable T S)
    (T : Tile) (S : Target) (k : Scale)
    (hbig : Tileable T (scale k S)) :
    ¬ P (data T S) :=
  no_similarity_invariant_proof Tileable scale data hdata P hsound T S k hbig

theorem sr_target_similar (m : Nat) : side m = m * side 1 ∧ base m = m * base 1 :=
  target_similar m

theorem sr_targets_concrete :
    side 1 = 8 ∧ base 1 = 11 ∧ side 2 = 16 ∧ base 2 = 22 ∧ side 3 = 24 ∧ base 3 = 33 :=
  targets_concrete

theorem sr_counts_concrete : count 1 = 11 ∧ count 2 = 44 ∧ count 3 = 99 := counts_concrete

theorem sr_side_no_b_m1 (P Q R : Nat)
    (hlen : 2 * P + 3 * Q + 4 * R = 8) (hR : 1 ≤ R) (hcorner : Q + 2 ≤ P + Q + R) :
    Q = 0 :=
  side_no_b_m1 P Q R hlen hR hcorner

theorem sr_side_b_exists_m2 :
    2 * 3 + 3 * 2 + 4 * 1 = 16 ∧ 1 ≤ 1 ∧ 2 + 2 ≤ 3 + 2 + 1 ∧ 2 ≠ 0 :=
  side_b_exists_m2

theorem sr_side_b_exists_m3 :
    2 * 7 + 3 * 2 + 4 * 1 = 24 ∧ 1 ≤ 1 ∧ 2 + 2 ≤ 7 + 2 + 1 ∧ 2 ≠ 0 :=
  side_b_exists_m3

-- Non-vacuity: concrete count
example : count 2 = 44 := sr_counts_concrete.2.1

#print axioms sr_no_similarity_invariant_proof
#print axioms sr_side_no_b_m1

end Erdos634.Draft.ScaleRigidityWrap
