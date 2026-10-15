/-
Draft/N60ACase.lean -- N = 60, Case A (`GapA 60`) modulo ONE explicit residual `GapA60Residual` (exceptional rows n = 30, 60), clone of N30Case at N = 60.
 * `N30Case.relTriv_smooth` is D-free and reused verbatim (n 5-smooth, 15 | n, n != 30, 60).
 * Lemma V at N = 60: v_3(60) = v_5(60) = 1 (odd), so 15 | n.
 * primes >= 7 dividing n: `NSQCaseA.r0c_core_nsq` (NQ 60, 60 not a sum of two squares, `HArith 60`) in place of `r0c_coreC`.  No sorry, no native_decide.
-/
import Mathlib
import Erdos634.Draft.N30Case
import Erdos634.Draft.NSQCaseA
import Erdos634.Draft.NSQMain
import Erdos634.Draft.N60AChain

open scoped BigOperators
open scoped Classical

namespace Erdos634.N60A

open Erdos634.Geometry Erdos634.LemmaS Erdos634.CaseA.R0c
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi lemmaV)
open Erdos634.Geometry.CaseA.LemmaH (HArith harith_of_bound)
open Erdos634.Draft.CompositeArith Erdos634.Draft.CompositeFinal2

theorem nsq_60 : ¬ ∃ x y : ℕ, 60 = x ^ 2 + y ^ 2 :=
  Erdos634.Draft.AllNExclusion.nsq_of_chk Erdos634.Draft.N60A.nsqChk_60

theorem harith_60 : HArith 60 :=
  harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The residual of `GapA 60`: only the exceptional rows `n = 30, 60`, and only tiles with `R != R_0`. -/
def GapA60Residual : Prop :=
  ∀ (D : CongruentDissection 60) (n : ℕ) (a : Fin 3 → ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, D.model.angleAt k = a k * Real.pi / n) →
    (n = 30 ∨ n = 60) → relSpace n a ≠ trivSpace n a → False

theorem val_60 (p : ℕ) (hp : p = 3 ∨ p = 5) : ¬ Even (padicValNat p 60) := by
  rcases hp with rfl | rfl
  · exact Nat.not_even_iff_odd.mpr <| val_one (p := 3) (k := 20) (by norm_num) (by norm_num) (by norm_num)
  · exact Nat.not_even_iff_odd.mpr <| val_one (p := 5) (k := 12) (by norm_num) (by norm_num) (by norm_num)

theorem fifteen_dvd_60 (D : CongruentDissection 60) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) : 15 ∣ n := by
  have hd : ∀ p : ℕ, p.Prime → (p = 3 ∨ p = 5) → p ∣ n := by
    intro p hp hp35
    by_contra h
    have hl : ¬ p ∣ 2 * n := by
      intro hh
      rcases (Nat.Prime.dvd_mul hp).mp hh with h' | h'
      · rcases hp35 with rfl | rfl <;> (have := Nat.le_of_dvd (by norm_num) h'; omega)
      · exact h h'
    exact val_60 p hp35 (lemmaV D hn a ha hp hl)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (hd 3 Nat.prime_three (Or.inl rfl))
    (hd 5 Nat.prime_five (Or.inr rfl))

/-- **GapAcomp 60 from the residual.** -/
theorem gapAcomp60_of_residual (R : GapA60Residual) : Erdos634.Draft.ChainComposite.GapAcomp 60 := by
  intro hS D hrat
  obtain ⟨n₀, hn₀, a₀, ha₀⟩ := exists_nat_angles D.model hrat
  obtain ⟨n, hn, a, hgcd, ha⟩ := exists_primitive D.model hn₀ a₀ ha₀
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have h15 := fifteen_dvd_60 D hn a ha
  have h15n : 15 ≤ n := Nat.le_of_dvd hn h15
  have core : relSpace n a = trivSpace n a → False := fun hSn =>
    Erdos634.Draft.NSQCaseA.r0c_core_nsq D (Erdos634.Draft.NSQMain.nq_of_chk Erdos634.Draft.N60A.nqChk_60)
      nsq_60 harith_60 hn a ha hSn (by omega)
  by_cases hp : ∃ p : ℕ, p.Prime ∧ 7 ≤ p ∧ p ∣ n
  · obtain ⟨p, hpp, hp7, hpn⟩ := hp
    exact core (hS n a hpos hsum hgcd p hpp hp7 hpn)
  · push Not at hp
    have hsm : ∀ p : ℕ, p.Prime → p ∣ n → p < 7 := fun p hpp hpn => by
      by_contra hlt; push Not at hlt; exact absurd hpn (hp p hpp hlt)
    by_cases hex : n = 30 ∨ n = 60
    · by_cases hSn : relSpace n a = trivSpace n a
      · exact core hSn
      · exact R D n a hn hgcd ha hex hSn
    · push Not at hex
      exact core (Erdos634.N30Case.relTriv_smooth n a hn hpos hsum hgcd h15 hsm hex.1 hex.2)

/-- **`GapA 60` from the residual** (Lemma S is proved and N-free). -/
theorem gapA60_of_residual (R : GapA60Residual) : Erdos634.Draft.Chain15.GapA 60 :=
  gapAcomp60_of_residual R Erdos634.LemmaSAll.lemmaS

end Erdos634.N60A

#print axioms Erdos634.N60A.harith_60
#print axioms Erdos634.N60A.fifteen_dvd_60
#print axioms Erdos634.N60A.gapA60_of_residual
