/-
GA2O, base: exact accounting of `GapA2` (CaseAN15.lean:27) and the two cheapest pieces.

`GapA2` quantifies over: D : CongruentDissection 15, n > 0, a : Fin 3 -> N with gcd(a) = 1, model angles a_k pi / n,
every prime factor of n < 7.  (Positivity of the a_k is not a hypothesis; it is derived from the angles.)

Pieces proved here (all new, unaudited, formalization of paper-level / finite-check mathematics):
* `fifteen_dvd`        : 15 | n for every such (D, n, a)   (Lemma V at l = 3, 5, v_l(15) = 1 odd; no 5-smoothness needed).
                         Hence the rows 15 !| n of the 5-smooth family are vacuous.
* `allCert_15`         : `LemmaS.allCert 15 = true` by `decide +kernel`  (Corollary-F certificate machinery of CaseACorF).
* `lemmaS_15`          : R(a) = R_0(a) for every primitive 3-tile with n = 15.
* `gapA2_n15`          : the n = 15 instance of GapA2 (n = 15, any D, a): False, via `r0c_core15` + `lemmaH15_holds`.
* `gapA2_of_rest`      : GapA2 follows from the statement `GapA2Rest` (= GapA2 plus 15 | n and n != 15).
Witnesses: `lemmaS_15_witness` (tile (1,1,13), R_0 != 0 so the n = 15 statement is not `bot = bot`), `allCert_15` negative
control `allCert_10_false` (n = 10 is where Lemma S fails: the certificate machinery does reject).
-/
import Mathlib
import Erdos634.Draft.CaseACorF
import Erdos634.Draft.CaseALemmaVDissection
import Erdos634.Draft.CaseAN15
import Erdos634.Draft.Chain15H

open scoped BigOperators

namespace Erdos634.GA2OBase

open Erdos634.Geometry Erdos634.LemmaS
open Erdos634.CaseA.R0c Erdos634.CaseA.R0c15
open Erdos634.Geometry.CaseA.LemmaV (lemmaV nat_bounds angle_pos angle_lt_pi)

theorem allCert_15 : allCert 15 = true := by decide +kernel

/-- The certificate checker rejects n = 10 (where Lemma S is false). -/
theorem allCert_10_false : allCert 10 = false := by decide +kernel

theorem lemmaS_15 (a : Fin 3 → ℕ) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = 15)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) : relSpace 15 a = trivSpace 15 a :=
  of_allCert allCert_15 a hpos hsum hgcd

theorem lemmaS_15_witness : relSpace 15 ![1, 1, 13] = trivSpace 15 ![1, 1, 13] :=
  lemmaS_15 _ (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three]) (by decide)

/-- R_0 is nonzero at (1,1,13): the statement is not `bot = bot`. -/
theorem trivSpace_15_witness_ne_bot : trivSpace 15 ![1, 1, 13] ≠ ⊥ := by
  intro h
  have hm : (1 : ℚ) • (Pi.single 0 1 - Pi.single 1 1 : Fin 3 → ℚ) ∈ trivSpace 15 ![1, 1, 13] :=
    pair_mem (n := 15) (a := ![1, 1, 13]) (i := 0) (j := 1) (by decide) (by simp) 1
  rw [h, Submodule.mem_bot] at hm
  have := congrFun hm 0
  simp at this

/-- **GapA2 at n = 15.** -/
theorem gapA2_n15 (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) (h15 : n = 15) : False := by
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  subst h15
  exact r0c_core15 D rfl hn a ha (lemmaS_15 a hpos hsum hgcd) (by norm_num)
    Erdos634.Draft.Chain15.lemmaH15_holds

/-- **15 | n** for any tile of any congruent dissection with N = 15. -/
theorem fifteen_dvd (D : CongruentDissection 15) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) : 15 ∣ n := by
  have h3 : 3 ∣ n := by
    by_contra h
    have hl : ¬ 3 ∣ 2 * n := by
      intro hh
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hh with h' | h'
      · omega
      · exact h h'
    haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hev := lemmaV D hn a ha Nat.prime_three hl
    have : padicValNat 3 15 = 1 := by
      have : (15 : ℕ) = 3 * 5 := by norm_num
      rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this] at hev
    exact absurd hev (by decide)
  have h5 : 5 ∣ n := by
    by_contra h
    have hl : ¬ 5 ∣ 2 * n := by
      intro hh
      rcases (Nat.Prime.dvd_mul Nat.prime_five).mp hh with h' | h'
      · omega
      · exact h h'
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    have hev := lemmaV D hn a ha Nat.prime_five hl
    have : padicValNat 5 15 = 1 := by
      have : (15 : ℕ) = 3 * 5 := by norm_num
      rw [this, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this] at hev
    exact absurd hev (by decide)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h3 h5

/-- GapA2 with the two finished pieces split off: 15 | n (automatic) and n != 15. -/
def GapA2Rest : Prop :=
  ∀ (D : CongruentDissection 15) (n : ℕ) (a : Fin 3 → ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, D.model.angleAt k = a k * Real.pi / n) →
    (∀ p : ℕ, p.Prime → p ∣ n → p < 7) → 15 ∣ n → n ≠ 15 → False

theorem gapA2_of_rest (H : GapA2Rest) : GapA2 := by
  intro D n a hn hgcd ha hsm
  by_cases h15 : n = 15
  · exact gapA2_n15 D n a hn hgcd ha h15
  · exact H D n a hn hgcd ha hsm (fifteen_dvd D hn a ha) h15

end Erdos634.GA2OBase

#print axioms Erdos634.GA2OBase.allCert_15
#print axioms Erdos634.GA2OBase.allCert_10_false
#print axioms Erdos634.GA2OBase.lemmaS_15
#print axioms Erdos634.GA2OBase.lemmaS_15_witness
#print axioms Erdos634.GA2OBase.trivSpace_15_witness_ne_bot
#print axioms Erdos634.GA2OBase.gapA2_n15
#print axioms Erdos634.GA2OBase.fifteen_dvd
#print axioms Erdos634.GA2OBase.gapA2_of_rest
