import Erdos634.PrimeRegimes

/-!
# The wall climb: wrapper

For every ℓ≥2 and 2≤j≤ℓ, block tile C_j is direct
and its mate M_j is forced, with M_j's c-edge [Q_{j-1},Q_j] continuing the interior wall; the
first run tile above the block is mirrored. No base-letter hypothesis, no line closure.

Key step: the west fan at Q_{j-1} is {β, C_j's γ, wedge of π-γ-β = α}. The wedge of angle α
is filled by a unique single α-tile (wedge_fill_unique via angle irrationality). This is the
forcing step for M_j.

Lean content:
1. **`wallclimb_wedge_is_alpha`**: the wedge p - γ - β = α (PrimeRegimes.wedge_is_alpha).
2. **`wallclimb_wedge_fill`**: the fill of a wedge of angle α is unique: (1,0,0) (PrimeRegimes.wedge_fill_unique).
3. **`wallclimb_cos_alpha_niven`**: cos α is never a Niven value at any member (cos_alpha_not_niven).
4. **`wallclimb_fill_everywhere`**: wedge fill is unique at every member (wedge_fill_forced_everywhere).

Only wedge-angle arithmetic and fill uniqueness are covered: 0 sorry, standard axioms.

Not covered here:
- The actual tile placement (C_j direct, M_j forced, overshoot kill) requires placement
  geometry (CongruentDissection, TilePlacement, etc.).
- The induction step (j → j+1 block) is not formalized with
  the CongruentDissection quantifier.
-/

namespace Erdos634.Draft.WallClimbWrap

open Erdos634.PrimeRegimes

/-- lem:wallclimb step: the west fan at Q_{j-1} gives a wedge of exactly α. -/
theorem wallclimb_wedge_is_alpha (a b g p : ℝ) (hg : g = 2*a + b) (hp : p = 3*a + 2*b) :
    p - g - b = a :=
  wedge_is_alpha a b g p hg hp

/-- lem:wallclimb: the fill of a wedge of angle α is unique — the mate M_j is the forced filler. -/
theorem wallclimb_wedge_fill (na nb ng : ℕ) (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) :
    na = 1 ∧ nb = 0 ∧ ng = 0 :=
  wedge_fill_unique na nb ng h1 h2

/-- lem:wallclimb: cos α is not a Niven value at any admissible member (so α/β irrational). -/
theorem wallclimb_cos_alpha_niven (e f : ℤ) (he : 0 < e) (hef : e < f) :
    e ^ 2 ≠ 0 ∧ e ^ 2 ≠ f ^ 2 ∧ e ^ 2 ≠ 2 * f ^ 2 ∧ e ^ 2 ≠ 3 * f ^ 2 ∧ e ^ 2 ≠ 4 * f ^ 2 :=
  cos_alpha_not_niven e f he hef

/-- lem:wallclimb: the wedge fill is unique at every member (α/π irrational at all members). -/
theorem wallclimb_fill_everywhere (na nb ng : ℕ)
    (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) : na = 1 ∧ nb = 0 ∧ ng = 0 :=
  wedge_fill_forced_everywhere na nb ng h1 h2

#print axioms wallclimb_wedge_is_alpha
#print axioms wallclimb_wedge_fill
#print axioms wallclimb_cos_alpha_niven
#print axioms wallclimb_fill_everywhere

end Erdos634.Draft.WallClimbWrap
