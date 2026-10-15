import Erdos634.Draft.TheoremP6

/-!
# Prime exclusion (N ≡ 3 mod 4, N > 3): wrapper

- `theoremP_6`: ∀ N D, N.Prime → N%4=3 → 3<N → False
  (no prime N ≡ 3 mod 4 with N > 3 is a congruent-dissection tile count). 0 sorry, standard axioms.
-/

namespace Erdos634.Draft.TheoremP6Wrap

open Erdos634.Geometry

theorem tp6_theoremP_6 :
    ∀ (N : ℕ) (D : CongruentDissection N), N.Prime → N % 4 = 3 → 3 < N → False :=
  Erdos634.Draft.TheoremP6.theoremP_6

-- Non-vacuity: N = 7 is prime, 7%4=3, 7>3 — hypothesis is satisfiable.
-- (We cannot exhibit a dissection since there is none, but we can exhibit the N.)
example : (7 : ℕ).Prime ∧ 7 % 4 = 3 ∧ 3 < 7 := by norm_num

#print axioms tp6_theoremP_6

end Erdos634.Draft.TheoremP6Wrap
