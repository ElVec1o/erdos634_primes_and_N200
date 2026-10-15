import Mathlib.Tactic
import Erdos634.Draft.T30LPi3Enum
import Erdos634.Draft.T30LPi3Tile
import Erdos634.Draft.T30LL4T30
import Erdos634.Draft.T30LL3SideTile
import Erdos634.Draft.T30LC2Strong
import Erdos634.Draft.CompositeE5Gen
import Erdos634.Draft.LemmaPProof
import Erdos634.Draft.FDCScaleReduce
import Erdos634.Draft.T30LL3Wit
import Erdos634.Draft.T30Cert

/-!
# `E60Pair 60 30 6` and `GapE60 60`

`e60_pair_30_6 : E60Pair 60 30 6` is proved by the kernel-checked certificate `ReflS.MT30.not_dissection` (`Draft.T30Cert.e60_pair_30_6_cert`).
Combined with `gapE60_of_pairs_exc` (CompositeE5Gen) and a pairs60_60 table (arithmetic), this gives `GapE60 60`.

The pair (m₁, m₂) = (30, 6) forces the tile to be the T30 triangle with sides
  `sa = 9+√21`, `sb = 9-√21`, `sc = 12`
(opposite to angles `β`, `β`, `π/3` respectively) and the equilateral target side to be `5*sc = 60`.

Arithmetic (`r6_arith`, `r6_side_sixty`): from `SixtyData α a b c` + `30*(a+b-c) = 3*S` + `6*(a+b+c) = 3*S` where `S = D.target.oppLen 0`:
`a+b-c = S/10`, `a+b+c = S/2`, hence `c = S/5`, `a+b = 3S/10`.  With `SixtyData` (law of cosines):
`c² = a²+b²-ab` → `a-b = ±√(7S²/300)` → `{a,b} = {S(9+√21)/60, S(9-√21)/60}`.
Area count: `area(T30) = (√3/4)·sa·sb = 15√3` and `60·15√3 = (√3/4)·S²` give `S = 60`, so `a = sa` and `b = sb` (or vice versa).
Each equilateral side has length `60 = 2·sa + 2·sb + 2·sc`, i.e. two edges of each letter.

`every_triple_killed` is a standalone fact about the side-word rule model.
-/

set_option maxHeartbeats 400000

namespace Erdos634.Pi3Close

open Erdos634.Geometry Erdos634.TilePlacement Erdos634.C2Forward Erdos634.Pi3Enum
open Erdos634.Pi3Corner Erdos634.ChordWord
open Erdos634.Draft.CompositeE5Gen Erdos634.Draft.Chain15
open Erdos634.Draft.TheoremPConditional

/-- The T30 tile's sides sum: `sa + sb + sc = 30`. -/
theorem t30_sides_sum : sa + sb + sc = 30 := by
  unfold Erdos634.ChordWord.sa Erdos634.ChordWord.sb Erdos634.ChordWord.sc
  ring

/-- Two copies of each T30 tile side sum to 60: `2*sa + 2*sb + 2*sc = 60`. -/
theorem t30_double_sum : 2 * sa + 2 * sb + 2 * sc = 60 := by linarith [t30_sides_sum]

/-- R6 arithmetic: from `30*(a+b-c) = 3*S` and `6*(a+b+c) = 3*S` for a `SixtyData` triple,
derive `c = S/5` and `a+b = 3*S/10`. -/
theorem r6_arith {a b c S : ℝ} (h1 : 30 * (a + b - c) = 3 * S) (h2 : 6 * (a + b + c) = 3 * S) :
    c = S / 5 ∧ a + b = 3 * S / 10 := by
  constructor
  · linarith
  · linarith

/-- R6 arithmetic: from the two pair conditions and `SixtyData`, derive `S = 60` for the T30 pair.
(Proof: S/5 = c = sc = 12, so S = 60.) -/
theorem r6_side_sixty {a b c S : ℝ} (hS : 0 < S)
    (h1 : (30 : ℝ) * (a + b - c) = 3 * S) (h2 : (6 : ℝ) * (a + b + c) = 3 * S)
    (hc : c = sc) : S = 60 := by
  obtain ⟨hceq, -⟩ := r6_arith h1 h2
  rw [hc] at hceq
  simp only [Erdos634.ChordWord.sc] at hceq; linarith

/-!
## Side-word route

`E60Pair 60 30 6` is proved without any axiom by the kernel-checked certificate `ReflS.MT30.not_dissection` (`Draft.T30Cert.e60_pair_30_6_cert`), and
`e60_pair_30_6` below is that theorem.  The side-word route is not needed for `N = 60`;
`every_triple_killed` is kept as a standalone fact.
-/

/-- Every corner-coupled triple from `sides true 2` is killed by L3 or L4.
Follows from `Pi3Enum.every_triple_killed_x2` (decided by kernel), once membership in
`triples (sides true 2)` is established from the individual memberships and coupling booleans. -/
theorem every_triple_killed (s1 s2 s3 : List OEdge)
    (h1 : s1 ∈ Pi3Enum.sides true 2) (h2 : s2 ∈ Pi3Enum.sides true 2)
    (h3 : s3 ∈ Pi3Enum.sides true 2)
    (hc12 : Pi3Enum.coupled s1 s2 = true) (hc23 : Pi3Enum.coupled s2 s3 = true)
    (hc31 : Pi3Enum.coupled s3 s1 = true) :
    Pi3Enum.killed s1 s2 = true ∨ Pi3Enum.killed s2 s3 = true ∨ Pi3Enum.killed s3 s1 = true := by
  apply Pi3Enum.every_triple_killed_x2 (s1, s2, s3)
  unfold Pi3Enum.triples
  simp only [List.mem_flatMap]
  refine ⟨s1, h1, s2, h2, s3, h3, ?_⟩
  simp only [hc12, hc23, hc31, Bool.and_true, ite_true, List.mem_singleton]

/-- **E60Pair 60 30 6**: no equilateral-target dissection with the T30 tile.  Axiom-free: this is
`T30Cert.e60_pair_30_6_cert` (certificate `ReflS.MT30`). -/
theorem e60_pair_30_6 : Erdos634.Draft.CompositeE5Gen.E60Pair 60 30 6 :=
  Erdos634.Draft.T30Cert.e60_pair_30_6_cert

/-- **Pairs table for N = 60.**  The pairs (m₁, m₂) with m₁ · m₂ = 3 · 60 = 180, 1 ≤ m₂ < m₁ ≤ 60:
  (60, 3) — pin; (30, 6) — exceptional T30;
  (45, 4): D = 1441 > 0, ¬square, no non-neg linear solution;
  (36, 5): D = 721 > 0, ¬square, no non-neg linear solution;
  (20, 9), (18, 10), (15, 12) — D < 0, ¬square vacuously.

Pure arithmetic — provable by interval_cases + omega + nlinarith on each of the 7 pairs.
The sorry below is a placeholder for the formal proof; all cases are decidable. -/
theorem pairs60_60_table : ∀ m₁ m₂ : ℤ, 1 ≤ m₁ → m₁ ≤ 60 → 1 ≤ m₂ → m₂ ≤ 60 →
    m₁ * m₂ = 3 * (60 : ℤ) → m₂ < m₁ →
    (m₁ = 60 ∧ m₂ = 3) ∨ (m₁ = 30 ∧ m₂ = 6) ∨
    (¬ IsSquare ((m₁ + m₂) ^ 2 - 16 * (60 : ℤ)) ∧
      (0 ≤ (m₁ + m₂) ^ 2 - 16 * (60 : ℤ) →
        ∀ p r : ℤ, 0 ≤ p → 0 ≤ r → 2 * (60 : ℤ) ≠ p * (m₁ + m₂) + r * (m₁ - m₂))) := by
  intro m₁ m₂ hm1 hm1N hm2 hm2N hprod hlt
  -- Strategy: interval_cases on m₁; omega closes non-divisor cases;
  -- for the 7 pairs (60,3),(45,4),(36,5),(30,6),(20,9),(18,10),(15,12) use specific tactics.
  interval_cases m₁
  all_goals first
  | omega  -- no valid m₂ exists
  | (-- (60, 3): pin
     left; constructor <;> omega)
  | (-- (30, 6): exceptional T30 pair
     right; left; constructor <;> omega)
  | (-- (45, 4): D = 1441, 37²<1441<38²; linear: 120 ≠ p*49 + rr*41 for p,rr≥0
     right; right
     have hm2_eq : m₂ = 4 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun _ p rr hp hrr => ?_⟩
     · have h76 : 76 * r ≤ 2885 := by nlinarith [mul_self_nonneg (r - 38)]
       have h76' : 76 * r ≥ -2885 := by nlinarith [mul_self_nonneg (r + 38)]
       nlinarith [mul_nonneg (show (0 : ℤ) ≤ 37 - r by omega) (show (0 : ℤ) ≤ 37 + r by omega)]
     · omega)
  | (-- (36, 5): D = 721, 26²<721<27²; linear: 120 ≠ p*41 + rr*31 for p,rr≥0
     right; right
     have hm2_eq : m₂ = 5 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun _ p rr hp hrr => ?_⟩
     · have h54 : 54 * r ≤ 1457 := by nlinarith [mul_self_nonneg (r - 27)]
       have h54' : 54 * r ≥ -1457 := by nlinarith [mul_self_nonneg (r + 27)]
       nlinarith [mul_nonneg (show (0 : ℤ) ≤ 26 - r by omega) (show (0 : ℤ) ≤ 26 + r by omega)]
     · omega)
  | (-- (20, 9): D = (29²-960) = -119 < 0
     right; right
     have hm2_eq : m₂ = 9 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun hD _ _ _ _ => ?_⟩
     · nlinarith [mul_self_nonneg r]
     · norm_num at hD)
  | (-- (18, 10): D = (28²-960) = -176 < 0
     right; right
     have hm2_eq : m₂ = 10 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun hD _ _ _ _ => ?_⟩
     · nlinarith [mul_self_nonneg r]
     · norm_num at hD)
  | (-- (15, 12): D = (27²-960) = -231 < 0
     right; right
     have hm2_eq : m₂ = 12 := by omega
     subst hm2_eq
     refine ⟨fun ⟨r, hr⟩ => ?_, fun hD _ _ _ _ => ?_⟩
     · nlinarith [mul_self_nonneg r]
     · norm_num at hD)

/-- **`GapE60 60`** from `e60_pair_30_6` and the proved pairs table. -/
theorem gapE60_60 : GapE60 60 :=
  gapE60_of_pairs_exc 60 (by norm_num) 30 6 e60_pair_30_6 pairs60_60_table

end Erdos634.Pi3Close
