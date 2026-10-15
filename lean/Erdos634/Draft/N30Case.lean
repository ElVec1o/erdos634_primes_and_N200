/-
Draft/N30Case.lean -- N = 30, Case A (`GapAcomp 30`) modulo ONE explicit residual `GapAcomp30Residual` (the exceptional rows n = 30, 60).

(1) `relTriv_smooth`: a D-FREE master statement.  For every primitive positive 3-tile `a` of `n`, `15 | n`, `n` 5-smooth, `n != 30, 60`:
    `relSpace n a = trivSpace n a`.  It re-runs the case split of `GA2QG.gapA2_of_residual3`, but keeps only the N-free tile-arithmetic
    lemmas (`lemmaS5_i3 / i0 / i2 / i1 / D3 / K0 / K1 / Ka / Kb3 / KbJ1 / Kc3 / KcJ1`, `allCert_75/90`, `lemmaS_15`); no CongruentDissection.
(2) `gapAcomp30_of_residual`: GapAcomp 30 from `GapAcomp30Residual`, via `HArith 30` + `r0c_coreC` (primes >= 7), `relTriv_smooth` + `r0c_coreC` (5-smooth),
    Lemma V at N = 30 (3, 5 | n; v_3(30) = v_5(30) = 1).
(3) `chain_30_final'` with the single hypothesis `GapAcomp30Residual`.  No sorry, no native_decide.
-/
import Mathlib
import Erdos634.Draft.GA2WZ
import Erdos634.Draft.CompositeN30

open scoped BigOperators
open scoped Classical

namespace Erdos634.N30Case

open Erdos634.Geometry Erdos634.LemmaS Erdos634.CaseA.R0c
open Erdos634.Geometry.CaseA.LemmaV (nat_bounds angle_pos angle_lt_pi lemmaV)
open Erdos634.Geometry.CaseA.LemmaH (HArith harith_of_bound)

theorem conv {n m : ℕ} {a : Fin 3 → ℕ} (h : n = m) (hr : relSpace m a = trivSpace m a) :
    relSpace n a = trivSpace n a := by subst h; exact hr

/-- **D-free master.** -/
theorem relTriv_smooth (n : ℕ) (a : Fin 3 → ℕ) (hn : 0 < n) (hpos : ∀ i, 0 < a i) (hsum : ∑ i, a i = n)
    (hgcd : Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1) (h15 : 15 ∣ n)
    (hsm : ∀ p : ℕ, p.Prime → p ∣ n → p < 7) (h30 : n ≠ 30) (h60 : n ≠ 60) :
    relSpace n a = trivSpace n a := by
  obtain ⟨i, j, k, e⟩ := Erdos634.GA2Q.smooth_rep n hn hsm
  have hs : ∀ m, n = m → ∑ i, a i = m := fun m h => by rw [hsum, h]
  have hj : 1 ≤ j := by
    by_contra hj0
    have hj0 : j = 0 := by omega
    have h3 : 3 ∣ n := Dvd.dvd.trans (by norm_num) h15
    have hc : Nat.Coprime 3 n := by
      rw [e, hj0]
      simp only [pow_zero, mul_one]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
        (Nat.Coprime.pow_right _ (by norm_num))
    have := Nat.Coprime.eq_one_of_dvd hc h3
    omega
  have hk : 1 ≤ k := by
    by_contra hk0
    have hk0 : k = 0 := by omega
    have h5 : 5 ∣ n := Dvd.dvd.trans (by norm_num) h15
    have hc : Nat.Coprime 5 n := by
      rw [e, hk0]
      simp only [pow_zero, mul_one]
      exact Nat.Coprime.mul_right (Nat.Coprime.pow_right _ (by norm_num))
        (Nat.Coprime.pow_right _ (by norm_num))
    have := Nat.Coprime.eq_one_of_dvd hc h5
    omega
  by_cases hi3 : 3 ≤ i
  · have e' : n = 5 ^ k * (2 ^ ((i - 3) + 3) * 3 ^ j) := by
      rw [e, show i - 3 + 3 = i by omega]; ring
    exact conv e' (Erdos634.GA2NP7.lemmaS5_i3 k (i - 3) j hk hj a hpos (hs _ e') hgcd)
  by_cases hc1 : (i, j, k) = (0, 1, 2)
  · obtain ⟨rfl, rfl, rfl⟩ : i = 0 ∧ j = 1 ∧ k = 2 := by simpa [Prod.ext_iff] using hc1
    have e' : n = 75 := by rw [e]; norm_num
    exact conv e' (of_allCert Erdos634.GA2OFin.allCert_75 a hpos (hs _ e') hgcd)
  by_cases hc2 : (i, j, k) = (1, 2, 1)
  · obtain ⟨rfl, rfl, rfl⟩ : i = 1 ∧ j = 2 ∧ k = 1 := by simpa [Prod.ext_iff] using hc2
    have e' : n = 90 := by rw [e]; norm_num
    exact conv e' (of_allCert Erdos634.GA2OFin.allCert_90 a hpos (hs _ e') hgcd)
  by_cases hk1 : k = 1
  · subst hk1
    by_cases hj1 : j = 1
    · subst hj1
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl | rfl
      · have e' : n = 15 := by rw [e]; norm_num
        exact conv e' (Erdos634.GA2OBase.lemmaS_15 a hpos (hs _ e') hgcd)
      · exact absurd (by rw [e]; norm_num) h30
      · exact absurd (by rw [e]; norm_num) h60
    · have hj2 : 2 ≤ j := by omega
      have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
      rcases hi with rfl | rfl | rfl
      · have e' : n = 5 ^ 1 * (2 ^ 0 * 3 ^ j) := by rw [e]; ring
        exact conv e' (Erdos634.GA2PH.lemmaS5_i0 j hj2 a hpos (hs _ e') hgcd)
      · have e' : n = 5 ^ 1 * (2 ^ 1 * 3 ^ j) := by rw [e]; ring
        by_cases hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t
        · exact conv e' (Erdos634.GA2SY.lemmaS5_D3 Erdos634.GA2UH.d3_lab j hj2 a hpos (hs _ e') hgcd hT)
        · have h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t := fun t h5 h3t => hT ⟨t, h5, h3t⟩
          exact conv e' (Erdos634.GA2QD5.lemmaS5_i1 j hj2 a hpos (hs _ e') hgcd h3)
      · have e' : n = 5 ^ 1 * (2 ^ 2 * 3 ^ j) := by rw [e]; ring
        exact conv e' (Erdos634.GA2PH.lemmaS5_i2 j hj2 a hpos (hs _ e') hgcd)
  · have hk2 : 2 ≤ k := by omega
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · by_cases hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t
      · by_cases hj2 : 2 ≤ j
        · have e' : n = 5 ^ k * (2 ^ 0 * 3 ^ j) := by rw [e]; ring
          exact conv e' (Erdos634.GA2SN.lemmaS5_Kb3 k j hk2 hj2 a hpos (hs _ e') hgcd hT)
        · have hj1 : j = 1 := by omega
          subst hj1
          have e' : n = 5 ^ k * (2 ^ 0 * 3 ^ 1) := by rw [e]; ring
          exact conv e' (Erdos634.GA2SY.lemmaS5_KbJ1 Erdos634.GA2WC.kbJ1_lab k hk2 a hpos (hs _ e') hgcd hT)
      · have h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t := fun t h5 h3t => hT ⟨t, h5, h3t⟩
        have e' : n = 5 ^ k * (2 ^ 0 * 3 ^ j) := by rw [e]; ring
        exact conv e' (Erdos634.GA2QK5.lemmaS5_K0 k j hk hj a hpos (hs _ e') hgcd h3)
    · by_cases hT : ∃ t : Fin 3, ¬ 5 ∣ a t ∧ 3 ∣ a t
      · obtain ⟨t, ht5, ht3⟩ := hT
        have e' : n = 5 ^ k * (2 ^ 1 * 3 ^ j) := by rw [e]; ring
        by_cases hc : 2 ≤ j ∨ a t % 2 = 1
        · exact conv e' (Erdos634.GA2ST.lemmaS5_Kc3 k j hk2 hj a hpos (hs _ e') hgcd ⟨t, ht5, ht3, hc⟩)
        · push Not at hc
          have hj1 : j = 1 := by omega
          subst hj1
          exact conv e' (Erdos634.GA2SY.lemmaS5_KcJ1 Erdos634.GA2WD.kcJ1_lab k hk2 a hpos (hs _ e') hgcd
            ⟨t, ht5, ht3, by omega⟩)
      · have h3 : ∀ t, ¬ 5 ∣ a t → ¬ 3 ∣ a t := fun t h5 h3t => hT ⟨t, h5, h3t⟩
        have e' : n = 5 ^ k * (2 ^ 1 * 3 ^ j) := by rw [e]; ring
        exact conv e' (Erdos634.GA2QK5.lemmaS5_K1 k j hk hj (Or.inl hk2) a hpos (hs _ e') hgcd h3)
    · have e' : n = 5 ^ k * (2 ^ 2 * 3 ^ j) := by rw [e]; ring
      exact conv e' (Erdos634.GA2SH.lemmaS5_Ka k j hk2 hj a hpos (hs _ e') hgcd)

/-! ### Controls for `relTriv_smooth` -/

/-- non-vacuity: the master applies at n = 45 (15 | 45, 5-smooth, != 30, 60) to the tile (1, 2, 42). -/
theorem relTriv_witness : relSpace 45 ![1, 2, 42] = trivSpace 45 ![1, 2, 42] :=
  relTriv_smooth 45 _ (by norm_num) (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) (by norm_num)
    (fun p hp hpn => by
      have : p ∣ 3 ^ 2 * 5 := by simpa using hpn
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · have := hp.dvd_of_dvd_pow h; have := Nat.le_of_dvd (by norm_num) this; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega)
    (by norm_num) (by norm_num)

/-- a second witness in a K-row: n = 150 = 2*3*5^2 (row Kc, T even branch uses `kcJ1_lab`), tile (1, 3, 146)?  gcd 1, sum 150. -/
theorem relTriv_witness150 : relSpace 150 ![1, 3, 146] = trivSpace 150 ![1, 3, 146] :=
  relTriv_smooth 150 _ (by norm_num) (by intro i; fin_cases i <;> decide) (by simp [Fin.sum_univ_three])
    (by decide) (by norm_num)
    (fun p hp hpn => by
      have : p ∣ 2 * 3 * 5 ^ 2 := by simpa using hpn
      rcases (Nat.Prime.dvd_mul hp).mp this with h | h
      · rcases (Nat.Prime.dvd_mul hp).mp h with h | h <;> (have := Nat.le_of_dvd (by norm_num) h; omega)
      · have := hp.dvd_of_dvd_pow h; have := Nat.le_of_dvd (by norm_num) this; omega)
    (by norm_num) (by norm_num)

/-- The side condition `n != 30` of the master statement is necessary: the analogous statement is false at n = 10
(`LemmaS.negative_control_n10`); n = 30 is excluded by hypothesis. -/
theorem control_n10 : relSpace 10 ![1, 2, 7] ≠ trivSpace 10 ![1, 2, 7] := Erdos634.LemmaS.negative_control_n10

/-! ### N = 30 -/

theorem harith_30 : HArith 30 :=
  harith_of_bound (by norm_num) (by norm_num) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- The residual of `GapAcomp 30`: only the exceptional rows `n = 30, 60`, and only tiles with `R != R_0` (the rest close by `r0c_coreC`). -/
def GapAcomp30Residual : Prop :=
  ∀ (D : CongruentDissection 30) (n : ℕ) (a : Fin 3 → ℕ), 0 < n →
    Nat.gcd (a 0) (Nat.gcd (a 1) (a 2)) = 1 → (∀ k, D.model.angleAt k = a k * Real.pi / n) →
    (n = 30 ∨ n = 60) → relSpace n a ≠ trivSpace n a → False

theorem val_30 (p : ℕ) (hp : p = 3 ∨ p = 5) : ¬ Even (padicValNat p 30) := by
  rcases hp with rfl | rfl
  · haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have : padicValNat 3 30 = 1 := by
      have h : padicValNat 3 30 = padicValNat 3 (3 * 10) := by norm_num
      rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this]; exact Nat.not_even_one
  · haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have : padicValNat 5 30 = 1 := by
      have h : padicValNat 5 30 = padicValNat 5 (5 * 6) := by norm_num
      rw [h, padicValNat.mul (by norm_num) (by norm_num), padicValNat_self,
        padicValNat.eq_zero_of_not_dvd (by norm_num)]
    rw [this]; exact Nat.not_even_one

theorem fifteen_dvd_30 (D : CongruentDissection 30) {n : ℕ} (hn : 0 < n) (a : Fin 3 → ℕ)
    (ha : ∀ k, D.model.angleAt k = a k * Real.pi / n) : 15 ∣ n := by
  have hd : ∀ p : ℕ, p.Prime → (p = 3 ∨ p = 5) → p ∣ n := by
    intro p hp hp35
    by_contra h
    have hl : ¬ p ∣ 2 * n := by
      intro hh
      rcases (Nat.Prime.dvd_mul hp).mp hh with h' | h'
      · rcases hp35 with rfl | rfl <;> (have := Nat.le_of_dvd (by norm_num) h'; omega)
      · exact h h'
    exact val_30 p hp35 (lemmaV D hn a ha hp hl)
  exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) (hd 3 Nat.prime_three (Or.inl rfl))
    (hd 5 Nat.prime_five (Or.inr rfl))

/-- **GapAcomp 30 from the residual.** -/
theorem gapAcomp30_of_residual (R : GapAcomp30Residual) : Erdos634.Draft.ChainComposite.GapAcomp 30 := by
  intro hS D hrat
  obtain ⟨n₀, hn₀, a₀, ha₀⟩ := exists_nat_angles D.model hrat
  obtain ⟨n, hn, a, hgcd, ha⟩ := exists_primitive D.model hn₀ a₀ ha₀
  have hsum := sum_of_angles hn ha
  have hpos : ∀ i, 0 < a i := fun i => (nat_bounds hn (ha i) (angle_pos _ i) (angle_lt_pi _ i)).1
  have h15 := fifteen_dvd_30 D hn a ha
  have h15n : 15 ≤ n := Nat.le_of_dvd hn h15
  have core : relSpace n a = trivSpace n a → False := fun hSn =>
    Erdos634.CaseA.RComposite.r0c_coreC D Erdos634.Draft.CompositeN30.sqfree_30 (by norm_num) Erdos634.Draft.CompositeN30.nsq30 harith_30
      hn a ha hSn (by omega)
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
      exact core (relTriv_smooth n a hn hpos hsum hgcd h15 hsm hex.1 hex.2)

/-- **N = 30, modulo `GapAcomp30Residual` only.** -/
theorem chain_30_final' (R : GapAcomp30Residual) (D : CongruentDissection 30) : False :=
  Erdos634.Draft.CompositeN30.chain_30_final (gapAcomp30_of_residual R) D

end Erdos634.N30Case

#print axioms Erdos634.N30Case.relTriv_smooth
#print axioms Erdos634.N30Case.relTriv_witness
#print axioms Erdos634.N30Case.relTriv_witness150
#print axioms Erdos634.N30Case.harith_30
#print axioms Erdos634.N30Case.fifteen_dvd_30
#print axioms Erdos634.N30Case.gapAcomp30_of_residual
#print axioms Erdos634.N30Case.chain_30_final'
