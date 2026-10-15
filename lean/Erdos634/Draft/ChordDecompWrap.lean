import Erdos634.ChordDecomp

/-!
# Chord trace and area non-integrality: wrapper

Re-exports, under `cd_` names, results of `ChordDecomp`:
- `area_not_integral`: f⁴ ∤ 138·n² for 1 ≤ n < 49
- `admissible_range`: 2401 ∤ 138·(3i+7j)² for i ≤ 7, j ≤ 4 in range
- `area_never_integral`: f⁴ ∤ N·m² when f coprime to N and 1 ≤ m < f²
- `coprime_tight`: e coprime to 2e+1
- `flush_sum_le`: flush total ≤ 59
- `straddle_ne_nil`: straddle is nonempty

No `sorry`; standard axioms only.
-/

namespace Erdos634.Draft.ChordDecompWrap

open Erdos634.ChordDecomp

theorem cd_area_not_integral (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ 48) :
    ¬ (2401 ∣ 138 * n ^ 2) :=
  area_not_integral n h1 h2

theorem cd_admissible_range {i j : ℕ} (hi : i ≤ 7) (hj : j ≤ 4)
    (hpos : 1 ≤ 3 * i + 7 * j) (hlt : 3 * i + 7 * j < 49) :
    ¬ (2401 ∣ 138 * (3 * i + 7 * j) ^ 2) :=
  admissible_range hi hj hpos hlt

theorem cd_area_never_integral {N f m : ℕ} (hf : 0 < f) (hcop : Nat.Coprime N f)
    (h1 : 1 ≤ m) (h2 : m < f ^ 2) : ¬ (f ^ 4 ∣ N * m ^ 2) :=
  area_never_integral hf hcop h1 h2

theorem cd_coprime_tight (e : ℕ) : Nat.Coprime e (2 * e + 1) :=
  coprime_tight e

theorem cd_flush_sum_le (C : ChordTrace) : C.flush.sum ≤ 59 :=
  flush_sum_le C

theorem cd_straddle_ne_nil (C : ChordTrace) : C.straddle ≠ [] :=
  straddle_ne_nil C

-- Non-vacuity: area_never_integral with f=3, N=2, m=5
example : ¬ ((3 : ℕ) ^ 4 ∣ 2 * 5 ^ 2) :=
  cd_area_never_integral (by norm_num) (by decide) (by norm_num) (by norm_num)

#print axioms cd_area_never_integral
#print axioms cd_area_not_integral

end Erdos634.Draft.ChordDecompWrap
