import Erdos634.PrimeBranchRepair

/-!
# The ladder has a density-zero ceiling, and the corner-cut target that replaces it

## 1. The ceiling

Even with the second step of the ladder fully repaired and the third in its strongest form
(`ApexChordCriterion`, `f ≥ 2e²`), the ladder R1 to R6 proves "not a tile count" only for base-β
primes all of whose representations satisfy `f ≥ 2e²`.  Counted exactly:

| `X` | base-β primes `≤ X` | reachable | share |
|---|---|---|---|
| `10⁴` | 307 | 38 | **12.4 %** |
| `10⁵` | 2397 | 155 | **6.5 %** |
| `10⁶` | 19654 | 702 | **3.6 %** |

The share decreases; the asymptotic is `Θ(X^{−1/4})`.  The ladder yields a density-zero partial
result, not the prime case.

(Also counted: no base-β prime below `10⁶` has more than one representation.)

## 2. R4b is not a separate obstruction

Beeson Def. 9 makes an interior segment a union of tile boundaries, so no tile interior meets it.
With `apex_strict_middle` (the apex is the *strict* middle vertex for `π−γ`) the maximum chord `f·b`
is attained only by the full chord `AD`, so `|S| = f·b` forces `S = AD` as a point set, endpoints
on `∂T`, which is R4b.

Moreover `FloorDependsOnJPos` shows the floor consumes the `j > 0` clause of the second step, so
R1, R3, R4a and R4b are all downstream of R2.  The ladder has exactly one existence input.

## 3. The corner-cut target

> **(CC) CORNER-CUT THEOREM.**  In any `m = 1` base-β tiling, **each** base vertex is the apex of a
> triangle cut off by an essential complete cut running from the base to the adjacent leg, in one of
> the two `b`-directions at that vertex.

(CC) implies that the whole `m = 1` family fails, for every `(e,f)`, with no domain restriction and
no chord bound, via L1 to L5 below, of which L4 is formalized here.  (CC) fails at `N = 44`
(`m = 2`, where the second base corner carries only an inessential `k = 1` cut), and holds at
`N = 99`.

## 4. L4: the thick-regime branch of the direction ambiguity

If the two corner cuts have mixed orientation `A/B` in the **thick** regime `f² < ef + e²`, they are
disjoint and leave a base gap `L = (f−e)(e² + ef − f²) > 0` between two tile vertices, so `L` is a sum
of whole tile sides: `L = ua + vb + wc`.  Mod `f` (`a ≡ 0`, `b ≡ −e²`, `c ≡ 0`) this gives
`−ve² ≡ −e³`, so `v ≡ e (mod f)` and `v ≥ e`, whence `L ≥ e·b`.  But

> `e·b − L = f²(f − e) > 0`,

so `L < e·b`.  Contradiction. ∎  This closes the mixed-orientation branch left by `CevianUnique`,
which arises at `N = 83`.

Axiom-clean; no `sorry`.
-/

namespace Erdos634.LadderCeiling

/-- **The `L4` gap identity**: `e·b − L = f²(f − e)` where `L = (f−e)(e² + ef − f²)`. -/
theorem gap_identity (e f : ℤ) :
    e * (f ^ 2 - e ^ 2) - (f - e) * (e ^ 2 + e * f - f ^ 2) = f ^ 2 * (f - e) := by ring

/-- **The gap is strictly below `e·b`**, for every `0 < e < f`. -/
theorem gap_lt_eb {e f : ℤ} (he : 0 < e) (hef : e < f) :
    (f - e) * (e ^ 2 + e * f - f ^ 2) < e * (f ^ 2 - e ^ 2) := by
  have h : 0 < f ^ 2 * (f - e) := by
    have : 0 < f := lt_trans he hef
    have h2 : 0 < f - e := by omega
    positivity
  linarith [gap_identity e f]

/-- **The `b`-count of any representation of the gap is `≥ e`.**  Mod `f` the tile sides are
`a ≡ 0`, `b ≡ −e²`, `c ≡ 0`, so `L = ua + vb + wc` forces `v ≡ e (mod f)`; with `v ≥ 0` that gives
`v ≥ e`. -/
theorem gap_v_ge_e {e f v : ℤ} (he : 0 < e) (hef : e < f) (hv : 0 ≤ v)
    (hcong : f ∣ (v - e)) : e ≤ v := by
  rcases hcong with ⟨t, ht⟩
  rcases lt_or_ge v e with h | h
  · exfalso
    have hf : 0 < f := lt_trans he hef
    -- `v − e = f·t` with `−e ≤ v − e < 0` and `e < f`, so `−f < f·t < 0`, forcing `0 < t < 1`
    have hlo : -f < f * t := by omega
    have hhi : f * t < 0 := by omega
    have ht0 : t < 0 := by nlinarith
    have ht1 : -1 < t := by nlinarith
    omega
  · exact h

/-- **L4.**  In the thick regime the mixed `A/B` corner-cut configuration is impossible: the gap
would have to be a sum of whole tile sides with `b`-count `≥ e`, hence `≥ e·b`, but it is `< e·b`. -/
theorem L4_thick_mixed_impossible {e f u v w : ℤ} (he : 0 < e) (hef : e < f)
    (hu : 0 ≤ u) (hw : 0 ≤ w) (hv : 0 ≤ v) (hvge : e ≤ v)
    (hrep : (f - e) * (e ^ 2 + e * f - f ^ 2) = u * (e * f) + v * (f ^ 2 - e ^ 2) + w * f ^ 2) :
    False := by
  have hf : 0 < f := lt_trans he hef
  have hb : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have h1 : e * (f ^ 2 - e ^ 2) ≤ v * (f ^ 2 - e ^ 2) :=
    mul_le_mul_of_nonneg_right hvge hb.le
  have h2 : 0 ≤ u * (e * f) := mul_nonneg hu (by positivity)
  have h3 : 0 ≤ w * f ^ 2 := mul_nonneg hw (by positivity)
  have := gap_lt_eb he hef
  linarith [hrep, h1, h2, h3]

end Erdos634.LadderCeiling
