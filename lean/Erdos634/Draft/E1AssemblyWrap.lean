import Erdos634.E1Assembly

/-!
# E1Assembly: e=1 base walk assembly arithmetic, wrapper

Key results:
- `sum_eps_mod`: Σε mod f arithmetic
- `integral_forces_p_eq_q`: f ∣ (q-p) with |q-p|<f forces p=q
- `apex_multiple_of_f`: apex position is a multiple of f
- `apex_plus_edges`: additive step for apex
- `odd_edge_starts_low`: first odd edge starts below f²
- `left_index_lt_f`: left index of odd edge is < f
- `walk_dies`: propositional schema for the walk kill
- `walk_spans`: walk spans base by ring identity

No sorry, standard axioms.
-/

namespace Erdos634.Draft.E1AssemblyWrap

open Erdos634.E1Assembly

theorem e1a_sum_eps_mod (f p q : ℤ) :
    p * (3 * f ^ 2 - 1) - q * (f ^ 2 - 1) - (q - p) = f ^ 2 * (3 * p - q) :=
  sum_eps_mod f p q

theorem e1a_integral_forces_p_eq_q (f p q j : ℤ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hj : p + q = j) (hjf : j < f) (hdvd : f ∣ (q - p)) : p = q :=
  integral_forces_p_eq_q f p q j hp hq hj hjf hdvd

theorem e1a_apex_multiple_of_f (f p k : ℤ) :
    p * (3 * f ^ 2 - 1) - p * (f ^ 2 - 1) = 2 * f * (p * f) :=
  apex_multiple_of_f f p k

theorem e1a_apex_plus_edges (f p k : ℤ) : p * f + k * f = (p + k) * f :=
  apex_plus_edges f p k

theorem e1a_odd_edge_starts_low (f i : ℕ) (hf : 2 ≤ f) (hi : i < f) : i * f < f ^ 2 :=
  odd_edge_starts_low f i hf hi

theorem e1a_left_index_lt_f (f p q : ℕ) (hf : 2 ≤ f) (hq3 : 3 ≤ q) (hqf : q ≤ f)
    (hp2 : 2 ≤ p) (hne : p ≠ q) :
    (p < q → p - 1 < f) ∧ (q < p → q - 1 < f) :=
  left_index_lt_f f p q hf hq3 hqf hp2 hne

theorem e1a_walk_dies (startsLow interiorForbids : Prop)
    (h1 : startsLow) (h2 : startsLow → ¬ interiorForbids) (h3 : interiorForbids) : False :=
  walk_dies startsLow interiorForbids h1 h2 h3

theorem e1a_walk_spans (f : ℤ) :
    f * f + 1 * (f ^ 2 - 1) + 1 * f ^ 2 = 3 * f ^ 2 - 1 :=
  walk_spans f

-- Non-vacuity: walk spans at f=2
example : (2 : ℤ) * 2 + 1 * (2 ^ 2 - 1) + 1 * 2 ^ 2 = 3 * 2 ^ 2 - 1 :=
  e1a_walk_spans 2

#print axioms e1a_integral_forces_p_eq_q
#print axioms e1a_walk_spans

end Erdos634.Draft.E1AssemblyWrap
