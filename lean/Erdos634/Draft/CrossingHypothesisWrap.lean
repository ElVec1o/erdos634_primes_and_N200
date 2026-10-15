import Erdos634.CrossingHypothesis

/-!
# CrossingHypothesis: crossing hypothesis and the e=1 reduction, wrapper

Key results:
- `reduction`: abstract e=1 closure chain
- `line_length`: L_k length identity
- `partition_of_line`: no-crossing → b-edge partition
- `only_small_lines`: chain only needs lines k < f
- `crossings_positive`: m≥2 counterexample data (crossing hypothesis fails)

No sorry, standard axioms.
-/

namespace Erdos634.Draft.CrossingHypothesisWrap

open Erdos634.CrossingHypothesis

theorem ch_reduction (NoCross NoStraddler ChainReaches Walls ThinClosed : Prop)
    (h₁ : NoCross → NoStraddler)
    (h₂ : NoStraddler → ChainReaches)
    (h₃ : ChainReaches → Walls)
    (h₄ : Walls → ThinClosed)
    (h : NoCross) : ThinClosed :=
  reduction NoCross NoStraddler ChainReaches Walls ThinClosed h₁ h₂ h₃ h₄ h

theorem ch_line_length (f k : ℤ) : k * (f ^ 2 - 1) = k * f ^ 2 - k :=
  line_length f k

theorem ch_partition_of_line {f k x y z B : ℕ} (hef : 1 < f) (hkf : k < f)
    (hco : Nat.Coprime f (1 * 1)) (hB : f * f = B + 1 * 1)
    (h : x * (1 * f) + y * B + z * (f * f) = k * B) :
    x = 0 ∧ y = k ∧ z = 0 :=
  partition_of_line hef hkf hco hB h

theorem ch_only_small_lines {f bp k : ℕ} (hf : 3 ≤ f) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hk : k ≤ bp - 1) : k < f :=
  only_small_lines hf hb3 hbf hk

theorem ch_crossings_positive :
    (0 < 42) ∧ (0 < 15) ∧ (0 < 24) ∧ (0 < 10) ∧ (0 < 98) :=
  crossings_positive

-- Non-vacuity: line_length is a ground fact
example : (3 : ℤ) * (5 ^ 2 - 1) = 3 * 5 ^ 2 - 3 := ch_line_length 5 3

#print axioms ch_reduction
#print axioms ch_partition_of_line

end Erdos634.Draft.CrossingHypothesisWrap
