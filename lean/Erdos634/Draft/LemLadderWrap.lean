import Erdos634.OrderForcing
import Erdos634.LadderInvariant

/-!
# Descent identities and the ladder: wrapper

At f≥3, a straddler forces a doubly-edged ladder with specific arithmetic properties.

(i) Descent identities: a b-direction line crosses strip lines at intervals of exactly b
along itself, advancing exactly c horizontally per crossing.
- `descent_ident`: fu_x + b|cos 2γ| = c ↔ (3f²-1) + (f²-1)(2f²-1) = 2f⁴
- `sinb_ident`: sin β has closed form b√D/(2f³), D=4f²-1 ↔ 4f⁶-(3f²-1)²=(f²-1)²(4f²-1)

(ii) Ladder step identity: the straddler's c-edge covers the run tile's b and pokes one unit past.
- `ladder_step_identity` (LadderInvariant)

(iii) No base exit: the termination abscissa forces f²|K, but K = (j-1)f+i with i≢0 mod f.
- `ladder_no_base` (OrderForcing)

(iv) Termination needs consecutive members of S=⟨f,f²-1,f²⟩: consecutive members start at f².
- `consecutive_gap` (OrderForcing)

Lean content:
1. **`lemladder_descent_ident`**: algebraic identity (i), ring proof.
2. **`lemladder_sinb_ident`**: sin β discriminant identity (i), ring proof.
3. **`lemladder_no_base`**: no base exit: f²|K and K%f≠0 are contradictory (iii).
4. **`lemladder_consecutive_gap`**: consecutive members of S start at f² (iv).
5. **`lemladder_step_identity`**: ladder step identity (ii), LadderInvariant.

No sorry; standard axioms.

Not formalized here: the geometric construction of the doubly-edged ladder (tiles placed, east/west cover
staggered by c-b=1), and the forcing of adjacent tiles by a straddler.
-/

namespace Erdos634.Draft.LemLadderWrap

open Erdos634.OrderForcing Erdos634.LadderInvariant Erdos634.Geometry

/-- lem:ladder (i): fu_x + b|cos 2γ| = c descent identity (ring proof). -/
theorem lemladder_descent_ident (f : ℤ) :
    (3 * f ^ 2 - 1) + (f ^ 2 - 1) * (2 * f ^ 2 - 1) = 2 * f ^ 4 :=
  descent_ident f

/-- lem:ladder (i): sin β discriminant identity (ring proof). -/
theorem lemladder_sinb_ident (f : ℤ) :
    4 * f ^ 6 - (3 * f ^ 2 - 1) ^ 2 = (f ^ 2 - 1) ^ 2 * (4 * f ^ 2 - 1) :=
  sinb_ident f

/-- lem:ladder (iii): no base exit — K%f≠0 and f²|K is a contradiction. -/
theorem lemladder_no_base {f K : ℕ} (h : K % f ≠ 0) : ¬ (f * f ∣ K) :=
  ladder_no_base h

/-- lem:ladder (iv): consecutive members of S=⟨f,f²-1,f²⟩ start at f². -/
theorem lemladder_consecutive_gap {f m x1 y1 z1 x2 y2 z2 : ℕ} (hf : 3 ≤ f)
    (h1 : x1 * f + y1 * (f * f - 1) + z1 * (f * f) = m)
    (h2 : x2 * f + y2 * (f * f - 1) + z2 * (f * f) = m + 1) :
    f * f ≤ m + 1 :=
  consecutive_gap hf h1 h2

/-- lem:ladder (ii): ladder step identity — distance from stagger point to next pin is b. -/
theorem lemladder_step_identity (a b c w₁ w₂ : ℝ) (ha : 0 < a) (hc : 0 < c)
    (hunit : w₁ ^ 2 + w₂ ^ 2 = 1) (hcos : 2 * a * c * w₁ = a ^ 2 + c ^ 2 - b ^ 2) :
    (c * w₁ - a) ^ 2 + (c * w₂) ^ 2 = b ^ 2 :=
  ladder_step_identity a b c w₁ w₂ ha hc hunit hcos

#print axioms lemladder_descent_ident
#print axioms lemladder_no_base
#print axioms lemladder_consecutive_gap
#print axioms lemladder_step_identity

end Erdos634.Draft.LemLadderWrap
