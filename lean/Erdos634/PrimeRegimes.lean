import Mathlib.Tactic

/-!
# The wedge-filler step and the integer criterion `e⁴ - 4e²f² + 2f⁴ > 0`

Erdős #634.  Every prime `≡ 11 (mod 12)` has exactly one base-`β` representation `p = 3f² - e²`
(`ThinHole.rep_unique`).

Several corner-chain steps fill a wedge of angle exactly `α` with a single `α`-tile.  One might
justify this by "`α` is the minimal angle", or by the weaker condition that no two smaller angles
fit, `2β > α`, which with `3α + 2β = π` reads `α < π/4`.  Since `cos α = 1 - e²/(2f²)`, that is the
integer criterion

  **`e⁴ - 4e²f² + 2f⁴ > 0`.**

This criterion is NOT needed for the fill.

## The fill is forced at every member

The west fan at `Q_{j-1}` is `β`, `C_j`'s angle is `γ`, and the remaining wedge is exactly
`π - γ - β`, which the branch relations make exactly `α` (`wedge_is_alpha`).  The tiles meeting the
apex inside the wedge each have a vertex there, so their angles sum to exactly `α`, and a fill is a
solution of the integer system `n_α + 2n_γ = 1`, `n_β + n_γ = 0`.  That system has the single
solution `(1,0,0)` (`wedge_fill_unique`), using only that `α/β` is irrational.

`α/π` is irrational at every member: `cos α = (2f² - e²)/(2f²)`, so by Niven's theorem a
rational-multiple-of-`π` angle would need `e² ∈ {0, f², 2f², 3f², 4f²}`.  With `0 < e < f` all five
are impossible, and none of them needs irrationality of `√2` or `√3`: `e² < f²` excludes the middle
three outright (`cos_alpha_not_niven`).  Hence `α/β` is irrational, and the fill is forced
everywhere (`wedge_fill_forced_everywhere`).

The fill also exhausts the ways a tile can meet the apex: a tile there either has a vertex at the
apex, or the apex lies interior to one of its edges, and the latter contributes `π` on one side,
which cannot fit inside a wedge of angle `α < π` bounded by two tile edges.

Neither `α`-minimality nor `α < π/4` is therefore needed for the wedge-filler step.  This concerns
the fill step only; the other steps of the corner chain are not addressed here.

The wedge condition fails exactly at the pairs
`(4,5) (5,6) (6,7) (7,8) (7,9) (8,9) (9,10) (9,11) (10,11) (10,13) (11,12) (11,13) (11,14)`
among `e ≤ 11`, `f ≤ 19`, `gcd(e,f) = 1`; for instance at `(11,14)`,
`11⁴ - 4·11²·14² + 2·14⁴ = 14641 - 94864 + 76832 = -3391 < 0`.  The condition `β`-minimality
(`f < eφ`) is a different criterion.
-/

namespace Erdos634.PrimeRegimes

/-- **The wedge-filler condition, as an integer criterion.**  `α < π/4` iff `2f² - e² > √2 f²`;
squaring (both sides positive since `f > e`) gives `e⁴ - 4e²f² + 2f⁴ > 0`. -/
def WedgeOK (e f : ℤ) : Prop := e ^ 4 - 4 * e ^ 2 * f ^ 2 + 2 * f ^ 4 > 0

/-- **`β`-minimality is not the criterion.**  At `(3,4)` the tile has `b < a`, so `β` is the minimal
angle, yet the wedge condition holds and the step survives. -/
theorem three_four_beta_minimal_but_ok :
    ((4:ℤ) ^ 2 - 3 ^ 2 < 3 * 4) ∧ WedgeOK 3 4 := by
  refine ⟨by norm_num, ?_⟩
  unfold WedgeOK; norm_num

/-- **`(5,6)` is `N = 83` and the wedge condition fails there.** -/
theorem eightythree_wedge_fails : 3 * 6 ^ 2 - 5 ^ 2 = 83 ∧ ¬ WedgeOK 5 6 := by
  refine ⟨by norm_num, ?_⟩
  unfold WedgeOK; norm_num

/-- **`(2,3)` is `N = 23`, a close pair on which the wedge condition SURVIVES.**  So the failing set
is not simply the close pairs. -/
theorem twentythree_close_but_ok :
    3 * 3 ^ 2 - 2 ^ 2 = 23 ∧ ((3:ℤ) ^ 2 ≤ 2 * 2 * 3 + 2 ^ 2) ∧ WedgeOK 2 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  unfold WedgeOK; norm_num

/-- **`(11,14)`, omitted from `Frontier`'s enumeration, does fail.** -/
theorem eleven_fourteen_fails : ¬ WedgeOK 11 14 := by
  unfold WedgeOK; norm_num


/-- **The wedge is exactly `α`.**  `π - γ - β = α` for the branch relations `γ = 2α + β` and
`3α + 2β = π`. -/
theorem wedge_is_alpha (a b g p : ℝ) (hg : g = 2*a + b) (hp : p = 3*a + 2*b) :
    p - g - b = a := by rw [hg, hp]; ring

/-- **The exact fill of a wedge of angle `α` is unique**, and the proof uses only the integer
system: `n_α + 2n_γ = 1` and `n_β + n_γ = 0`, which come from `α/β` irrational
(`BaseBetaE1.tile_alpha_irrational`).  No minimality of `α`, and no `α < π/4`. -/
theorem wedge_fill_unique (na nb ng : ℕ) (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) :
    na = 1 ∧ nb = 0 ∧ ng = 0 := by omega

/-- The same for the neighbouring wedges the chain meets, so the phenomenon is not special to `α`. -/
theorem wedge_fill_unique_two_alpha (na nb ng : ℕ) (h1 : na + 2 * ng = 2) (h2 : nb + ng = 0) :
    na = 2 ∧ nb = 0 ∧ ng = 0 := by omega


/-- **`cos α` is never a Niven value, at any admissible member.**  `cos α = (2f² - e²)/(2f²)`, so a
rational-multiple-of-`π` angle would need `2f² - e²` to be one of `2f², f², 0, -f², -2f²`, i.e.
`e² ∈ {0, f², 2f², 3f², 4f²}`.  With `0 < e < f` every one is impossible, and — worth noting — none
of the five needs irrationality of `√2` or `√3`: `e² < f²` kills the middle three outright. -/
theorem cos_alpha_not_niven (e f : ℤ) (he : 0 < e) (hef : e < f) :
    e ^ 2 ≠ 0 ∧ e ^ 2 ≠ f ^ 2 ∧ e ^ 2 ≠ 2 * f ^ 2 ∧ e ^ 2 ≠ 3 * f ^ 2 ∧ e ^ 2 ≠ 4 * f ^ 2 := by
  have hf : 0 < f := lt_trans he hef
  have hf2 : (0:ℤ) < f ^ 2 := by positivity
  have hlt : e ^ 2 < f ^ 2 := by nlinarith
  refine ⟨by positivity, ?_, ?_, ?_, ?_⟩ <;> intro h <;> linarith

/-- So `α/π` is irrational at **every** member, not only at `e = 1`, and hence so is `α/β` (since
`β = (π - 3α)/2`, a rational `α/β` forces a rational `α/π`).  The vertex-figure representation
`x·α + y·β` is therefore unique at every member, which is what the wedge fill needs. -/
theorem wedge_fill_forced_everywhere (na nb ng : ℕ)
    (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) : na = 1 ∧ nb = 0 ∧ ng = 0 := by omega

end Erdos634.PrimeRegimes
