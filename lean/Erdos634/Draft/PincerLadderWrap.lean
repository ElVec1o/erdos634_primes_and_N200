import Erdos634.PincerLadder

/-!
# PincerLadder — pincer ladder reach and mirror symmetry: wrapper

Key results:
- `pincer_ladder`: four kills cover depth ≤ R for f ≤ R+1
- `ladder_reach_three/four`: R=4, R=5 specializations
- `pincer_sharp`: configuration (4,2) escapes at f=R+2
- `Kill`: four-case kill predicate
- `kill_mirror`: kills are mirror-symmetric
- `first_failure_escapes`: at f=R+2 escapes are exactly orbit of (4,2)
- `four_two_escapes/mirror_escapes/mirror`: (4,2) and its reflection

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.PincerLadderWrap

open Erdos634.PincerLadder

theorem pl_pincer_ladder {f bp cp R : ℕ} (hf : 3 ≤ f) (hfR : f ≤ R + 1)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ R) ∨ (cp < bp ∧ f + 3 - bp ≤ R) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ R) ∨ (bp = cp + 1 ∧ cp ≤ R) :=
  pincer_ladder hf hfR hb3 hbf hc2 hcf hne

theorem pl_ladder_reach_three {f bp cp : ℕ} (hf : 3 ≤ f) (hf5 : f ≤ 5)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 4) ∨ (cp < bp ∧ f + 3 - bp ≤ 4) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 4) ∨ (bp = cp + 1 ∧ cp ≤ 4) :=
  ladder_reach_three hf hf5 hb3 hbf hc2 hcf hne

theorem pl_ladder_reach_four {f bp cp : ℕ} (hf : 3 ≤ f) (hf6 : f ≤ 6)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 5) ∨ (cp < bp ∧ f + 3 - bp ≤ 5) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 5) ∨ (bp = cp + 1 ∧ cp ≤ 5) :=
  ladder_reach_four hf hf6 hb3 hbf hc2 hcf hne

theorem pl_pincer_sharp {R : ℕ} (hR : 4 ≤ R) :
    ¬ ((4 < 2 ∧ 4 ≤ R) ∨ (2 < 4 ∧ (R + 2) + 3 - 4 ≤ R) ∨
       (2 = 4 + 1 ∧ (R + 2) + 3 - 2 ≤ R) ∨ (4 = 2 + 1 ∧ 2 ≤ R)) :=
  pincer_sharp hR

theorem pl_kill_mirror (f bp cp R : ℕ) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) :
    Kill f (f + 3 - bp) (f + 3 - cp) R ↔ Kill f bp cp R :=
  kill_mirror f bp cp R hb3 hbf hc2 hcf

theorem pl_first_failure_escapes {R bp cp : ℕ} (hR : 4 ≤ R)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ R + 2) (hc2 : 2 ≤ cp) (hcf : cp ≤ R + 3) (hne : bp ≠ cp)
    (hesc : ¬ Kill (R + 2) bp cp R) :
    (bp = 4 ∧ cp = 2) ∨ (bp = R + 1 ∧ cp = R + 3) :=
  first_failure_escapes hR hb3 hbf hc2 hcf hne hesc

theorem pl_four_two_escapes {R : ℕ} (hR : 4 ≤ R) : ¬ Kill (R + 2) 4 2 R :=
  four_two_escapes hR

theorem pl_four_two_mirror_escapes {R : ℕ} (hR : 4 ≤ R) : ¬ Kill (R + 2) (R + 1) (R + 3) R :=
  four_two_mirror_escapes hR

theorem pl_four_two_mirror {R : ℕ} (hR : 4 ≤ R) :
    (R + 2 + 3 - 4, R + 2 + 3 - 2) = (R + 1, R + 3) :=
  four_two_mirror hR

-- Non-vacuity: (4,2) escapes at R=4
example : ¬ Kill 6 4 2 4 := pl_four_two_escapes (by norm_num)

#print axioms pl_pincer_ladder
#print axioms pl_first_failure_escapes

end Erdos634.Draft.PincerLadderWrap
