-- Draft/FDBPrimeWrappers.lean -- the main prime theorem, the mod-12 corollary and the full prime
-- characterization as Lean statements transcribed from the paper, each derived from
-- `TheoremP6.theoremP_6` / `PrimeCharacterization.prime_tile_count_iff`.
-- "N is a number of congruent triangles into which some triangle can be cut" is rendered as
-- `Nonempty (CongruentDissection N)` (any triangle, any tile, isometries incl. reflections, not
-- edge-to-edge, as in the paper's definition of an N-tiling).
-- Wrappers only.  This file proves nothing beyond `theoremP_6`.
-- Imported by `All`.  No sorry, no native_decide.
import Erdos634.Draft.TheoremP6
import Erdos634.Draft.PrimeCharacterization

namespace Erdos634.Draft.FDBPrimeWrappers
open Erdos634.Geometry

/-- Paper's "N is a tile count": some triangle is cut into `N` congruent triangles. -/
def IsTileCount (N : ℕ) : Prop := Nonempty (CongruentDissection N)

/-- **The main prime theorem, as written.**  Let `N > 3` be a prime with `N ≡ 3 (mod 4)`
which is not a base-β candidate, i.e. `N ≠ 3f² − e²` for every coprime pair `1 ≤ e < f`.
Then `N` is not a tile count.  (`3f² − e²` is read in `ℤ`; `e < f` makes it positive anyway.) -/
theorem thm_main_of_P6 (N : ℕ) (hN : N.Prime) (hN3 : 3 < N) (h4 : N % 4 = 3)
    (_hnb : ∀ e f : ℕ, 1 ≤ e → e < f → Nat.Coprime e f → (N : ℤ) ≠ 3 * (f : ℤ) ^ 2 - (e : ℤ) ^ 2) :
    ¬ IsTileCount N := by
  rintro ⟨D⟩
  exact Erdos634.Draft.TheoremP6.theoremP_6 N D hN h4 hN3

/-- The paper's "in particular": since `19` is not `3f² − e²` (coprime `1 ≤ e < f`), `thm_main_of_P6`
gives that no triangle can be cut into `19` congruent triangles. -/
theorem no_cut_19 : ¬ IsTileCount 19 := by
  refine thm_main_of_P6 19 (by norm_num) (by norm_num) (by norm_num) ?_
  intro e f he hef _ h
  push_cast at h
  have h2 : (e : ℤ) ≤ f - 1 := by
    have : (e : ℤ) + 1 ≤ f := by exact_mod_cast hef
    linarith
  have h3 : (e : ℤ) ≥ 1 := by exact_mod_cast he
  have hsq : (e : ℤ) * e ≤ (f - 1) * (f - 1) := mul_self_le_mul_self (by linarith) h2
  have hf : f ≤ 4 := by
    by_contra hcon
    push Not at hcon
    have h1 : (f : ℤ) ≥ 5 := by exact_mod_cast hcon
    nlinarith
  have he3 : e ≤ 3 := by omega
  interval_cases f <;> interval_cases e <;> omega

/-- **The mod-12 corollary, as written.**  No prime `p ≡ 7 (mod 12)` is a tile count.
Equivalently: a prime `p > 3` with `p ≡ 3 (mod 4)` is excluded unless `p ≡ 11 (mod 12)`. -/
theorem cor_mod12 (p : ℕ) (hp : p.Prime) (h7 : p % 12 = 7) : ¬ IsTileCount p := by
  rintro ⟨D⟩
  exact Erdos634.Draft.TheoremP6.theoremP_6 p D hp (by omega) (by omega)

/-- `cor:mod12`, the "equivalently" form. -/
theorem cor_mod12_equiv (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) (h4 : p % 4 = 3)
    (_hne : p % 12 ≠ 11) : ¬ IsTileCount p := by
  rintro ⟨D⟩
  exact Erdos634.Draft.TheoremP6.theoremP_6 p D hp h4 hp3

/-- **The full prime characterization, first sentence, as written.**  For a prime
`p ≢ 11 (mod 12)`: `p` is a tile count iff `p = 2`, `p = 3` or `p ≡ 1 (mod 4)`. -/
theorem thm_primefull (p : ℕ) (hp : p.Prime) (_h11 : p % 12 ≠ 11) :
    IsTileCount p ↔ (p = 2 ∨ p = 3 ∨ p % 4 = 1) := by
  have key := Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff p hp
  have hodd : p = 2 ∨ p % 2 = 1 := hp.eq_two_or_odd
  unfold IsTileCount
  rw [key]
  omega

/-- `thm:primefull`, STRONGER than the paper: the iff holds for EVERY prime (no `p ≢ 11 (mod 12)`
restriction); this is `prime_tile_count_iff` in the paper's own phrasing. -/
theorem thm_primefull_all (p : ℕ) (hp : p.Prime) :
    IsTileCount p ↔ (p = 2 ∨ p = 3 ∨ p % 4 = 1) := by
  have key := Erdos634.Draft.PrimeCharacterization.prime_tile_count_iff p hp
  have hodd : p = 2 ∨ p % 2 = 1 := hp.eq_two_or_odd
  unfold IsTileCount
  rw [key]
  omega

/-- `thm:primefull`, second sentence: the same equivalence for the listed `p ≡ 11 (mod 12)`
(`11, 23, 47, 59, 71, 107` and `83`).  Each is NOT a tile count.  (The paper says the "only if"
direction for the remaining `p ≡ 11 (mod 12)`, smallest `131`, is open; `theoremP_6` closes it,
so the Lean statement is STRONGER there, see `thm_primefull_all`.) -/
theorem thm_primefull_listed (p : ℕ) (hp : p.Prime)
    (_hl : p = 11 ∨ p = 23 ∨ p = 47 ∨ p = 59 ∨ p = 71 ∨ p = 107 ∨ p = 83) :
    IsTileCount p ↔ (p = 2 ∨ p = 3 ∨ p % 4 = 1) :=
  thm_primefull_all p hp

end Erdos634.Draft.FDBPrimeWrappers

#print axioms Erdos634.Draft.FDBPrimeWrappers.thm_main_of_P6
#print axioms Erdos634.Draft.FDBPrimeWrappers.no_cut_19
#print axioms Erdos634.Draft.FDBPrimeWrappers.cor_mod12
#print axioms Erdos634.Draft.FDBPrimeWrappers.cor_mod12_equiv
#print axioms Erdos634.Draft.FDBPrimeWrappers.thm_primefull
#print axioms Erdos634.Draft.FDBPrimeWrappers.thm_primefull_all
#print axioms Erdos634.Draft.FDBPrimeWrappers.thm_primefull_listed
