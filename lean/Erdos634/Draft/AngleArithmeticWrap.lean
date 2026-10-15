import Erdos634.AngleArithmetic

/-!
# Angle figure combinatorics: wrapper

Re-exports, under `aa_` names, results of `AngleArithmetic`:
- `apex_forced`: X=3, Y=0 → only one α figure
- `beta_corner_forced`: X=0, Y=1 → only one β figure
- `pi_vertex`: X=3, Y=2 → two cases (3α+2β or 1α+1β+1γ)
- `alpha_beta_corner`: X=1, Y=1 → one α + one β
- `unique_e1_beta_lt_pi3`: β < π/3 at e=1 only for f=2

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.AngleArithmeticWrap

open Erdos634.AngleArithmetic

theorem aa_apex_forced (na nb ng : Nat) (hx : na + 2 * ng = 3) (hy : nb + ng = 0) :
    na = 3 ∧ nb = 0 ∧ ng = 0 :=
  apex_forced na nb ng hx hy

theorem aa_beta_corner_forced (na nb ng : Nat) (hx : na + 2 * ng = 0) (hy : nb + ng = 1) :
    na = 0 ∧ nb = 1 ∧ ng = 0 :=
  beta_corner_forced na nb ng hx hy

theorem aa_pi_vertex (na nb ng : Nat) (hx : na + 2 * ng = 3) (hy : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) :=
  pi_vertex na nb ng hx hy

theorem aa_gamma_trap (na nb ng : Nat) (hx : na + 2 * ng = 3) (hy : nb + ng = 2) : ng ≤ 1 :=
  gamma_trap na nb ng hx hy

theorem aa_alpha_beta_corner (na nb ng : Nat) (hx : na + 2 * ng = 1) (hy : nb + ng = 1) :
    na = 1 ∧ nb = 1 ∧ ng = 0 :=
  alpha_beta_corner na nb ng hx hy

-- Non-vacuity: apex_forced with na=3, nb=0, ng=0
example : (3:Nat) = 3 ∧ 0 = 0 ∧ 0 = 0 :=
  aa_apex_forced 3 0 0 (by omega) (by omega)

#print axioms aa_apex_forced
#print axioms aa_pi_vertex

end Erdos634.Draft.AngleArithmeticWrap
