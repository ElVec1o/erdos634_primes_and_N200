/-
Draft/NSQRADvd.lean — The arithmetic hypothesis `NSQRA.RADvd N` (R-A / S5) for
`N = 8 m`, `m` odd squarefree, and (consistency) for every squarefree `N`.

`RADvd N`: coprime `0 < e < f`, `K > 0`, `N (f+e) = K² (f−e)`  ⇒  `N ∣ (f−e) K`.
Proof for `N = 8m` (`D = (f−e) K`, `D² = 8 m (f² − e²)`): (1) `e, f` both odd (opposite parity makes `m (f²−e²)` odd, but
`D² = 8·odd` has odd 2-adic valuation); (2) odd squares are `≡ 1 (8)`, so `8 ∣ f²−e²`, `64 ∣ D²`, `8 ∣ D`; (3) `m ∣ D²`, `m` squarefree ⇒
`m ∣ D`; (4) `Coprime 8 m`.
Negative: for N with an odd square factor p², or 2-adic valuation 2 or ≥ 4, `RADvd N` is FALSE (explicit solutions exist;
`not_radvd_76`: N = 76, (e, f, K) = (9, 10, 38): σ = 1/2).  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQRA

namespace Erdos634.Draft.NSQRA

theorem ra_dvd_of_squarefree {N : ℕ} (hN : Squarefree N) : RADvd N := by
  intro e f K he hef hcop hK hEq
  have hNsq : Squarefree (N : ℤ) := Int.squarefree_natCast.mpr hN
  have hk2 : ((f - e) * K) ^ 2 = N * (f ^ 2 - e ^ 2) := by
    have : ((f - e) * K) ^ 2 = (f - e) * (K ^ 2 * (f - e)) := by ring
    rw [this, ← hEq]; ring
  have hdvd : (N : ℤ) ∣ ((f - e) * K) ^ 2 := ⟨f ^ 2 - e ^ 2, hk2⟩
  exact (hNsq.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hdvd

theorem ra_dvd_of_eight (m : ℕ) (hm : Squarefree m) (hodd : m % 2 = 1) : RADvd (8 * m) := by
  intro e f K he hef hcop hK hEq
  have hm0 : 0 < m := by omega
  have hEq' : 8 * (m : ℤ) * (f + e) = K ^ 2 * (f - e) := by push_cast at hEq; exact hEq
  set D : ℤ := (f - e) * K with hD
  have hD2 : D ^ 2 = 8 * (m : ℤ) * (f ^ 2 - e ^ 2) := by
    have : D ^ 2 = (f - e) * (K ^ 2 * (f - e)) := by rw [hD]; ring
    rw [this, ← hEq']; ring
  have hmodd : (m : ℤ) % 2 = 1 := by omega
  -- coprime ⇒ not both even
  have hnb : ¬ (e % 2 = 0 ∧ f % 2 = 0) := by
    rintro ⟨h1, h2⟩
    obtain ⟨u, v, huv⟩ := hcop
    obtain ⟨a, ha⟩ : ∃ a, e = 2 * a := ⟨e / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, f = 2 * b := ⟨f / 2, by omega⟩
    have : 2 * (u * a + v * b) = 1 := by rw [ha, hb] at huv; linarith
    omega
  -- opposite parity is impossible
  have hboth : e % 2 = 1 ∧ f % 2 = 1 := by
    by_contra hcon
    have hcase : (e % 2 = 0 ∧ f % 2 = 1) ∨ (e % 2 = 1 ∧ f % 2 = 0) := by omega
    -- in both cases `f² − e²` is odd
    have hW : (f ^ 2 - e ^ 2) % 2 = 1 := by
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · obtain ⟨a, ha⟩ : ∃ a, e = 2 * a := ⟨e / 2, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, f = 2 * b + 1 := ⟨f / 2, by omega⟩
        have : f ^ 2 - e ^ 2 = 2 * (2 * b ^ 2 + 2 * b - 2 * a ^ 2) + 1 := by rw [ha, hb]; ring
        omega
      · obtain ⟨a, ha⟩ : ∃ a, e = 2 * a + 1 := ⟨e / 2, by omega⟩
        obtain ⟨b, hb⟩ : ∃ b, f = 2 * b := ⟨f / 2, by omega⟩
        have : f ^ 2 - e ^ 2 = 2 * (2 * b ^ 2 - 2 * a ^ 2 - 2 * a - 1) + 1 := by rw [ha, hb]; ring
        omega
    obtain ⟨c, hc⟩ : ∃ c, (m : ℤ) = 2 * c + 1 := ⟨(m : ℤ) / 2, by omega⟩
    obtain ⟨w, hw⟩ : ∃ w, f ^ 2 - e ^ 2 = 2 * w + 1 := ⟨(f ^ 2 - e ^ 2) / 2, by omega⟩
    -- `W = m (f²−e²)` is odd
    obtain ⟨W, hWdef⟩ : ∃ W, W = (m : ℤ) * (f ^ 2 - e ^ 2) := ⟨_, rfl⟩
    have hWodd : W % 2 = 1 := by
      have : W = 2 * (2 * c * w + c + w) + 1 := by rw [hWdef, hc, hw]; ring
      omega
    have hD2' : D ^ 2 = 8 * W := by rw [hD2, hWdef]; ring
    -- `D` even
    obtain ⟨D1, hD1⟩ : ∃ D1, D = 2 * D1 := by
      have : D % 2 = 0 := by
        by_contra h
        obtain ⟨t, ht⟩ : ∃ t, D = 2 * t + 1 := ⟨D / 2, by omega⟩
        have : D ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 := by rw [ht]; ring
        omega
      exact ⟨D / 2, by omega⟩
    have h4 : D1 ^ 2 = 2 * W := by
      have : 4 * D1 ^ 2 = 8 * W := by rw [← hD2', hD1]; ring
      linarith
    obtain ⟨D2, hD3⟩ : ∃ D2, D1 = 2 * D2 := by
      have : D1 % 2 = 0 := by
        by_contra h
        obtain ⟨t, ht⟩ : ∃ t, D1 = 2 * t + 1 := ⟨D1 / 2, by omega⟩
        have : D1 ^ 2 = 2 * (2 * t ^ 2 + 2 * t) + 1 := by rw [ht]; ring
        omega
      exact ⟨D1 / 2, by omega⟩
    have h5 : 2 * D2 ^ 2 = W := by
      have : 4 * D2 ^ 2 = 2 * W := by rw [← h4, hD3]; ring
      linarith
    omega
  obtain ⟨he1, hf1⟩ := hboth
  -- `8 ∣ f² − e²`
  have h8 : (8 : ℤ) ∣ f ^ 2 - e ^ 2 := by
    obtain ⟨a, ha⟩ : ∃ a, e = 2 * a + 1 := ⟨e / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, f = 2 * b + 1 := ⟨f / 2, by omega⟩
    have h1 : Even (b * (b + 1)) := Int.even_mul_succ_self b
    have h2 : Even (a * (a + 1)) := Int.even_mul_succ_self a
    obtain ⟨s1, hs1⟩ := h1
    obtain ⟨s2, hs2⟩ := h2
    refine ⟨s1 - s2, ?_⟩
    have : f ^ 2 - e ^ 2 = 4 * (b * (b + 1)) - 4 * (a * (a + 1)) := by rw [ha, hb]; ring
    rw [this, hs1, hs2]; ring
  obtain ⟨k8, hk8⟩ := h8
  have h64 : (8 : ℤ) ^ 2 ∣ D ^ 2 := ⟨(m : ℤ) * k8, by rw [hD2, hk8]; ring⟩
  have h8D : (8 : ℤ) ∣ D := (Int.pow_dvd_pow_iff (by norm_num : 2 ≠ 0)).mp h64
  have hmD2 : (m : ℤ) ∣ D ^ 2 := ⟨8 * (f ^ 2 - e ^ 2), by rw [hD2]; ring⟩
  have hmsq : Squarefree (m : ℤ) := Int.squarefree_natCast.mpr hm
  have hmD : (m : ℤ) ∣ D := (hmsq.dvd_pow_iff_dvd (by norm_num : 2 ≠ 0)).mp hmD2
  have hcop8 : IsCoprime (8 : ℤ) (m : ℤ) := by
    obtain ⟨c, hc⟩ : ∃ c, (m : ℤ) = 2 * c + 1 := ⟨(m : ℤ) / 2, by omega⟩
    -- 8 * (-c ... ) : (2c+1)*(a) + 8 * (b) = 1 ; use  m * m' ≡ 1 mod 8 via IsCoprime of 2 and m
    have h2m : IsCoprime (2 : ℤ) (m : ℤ) := ⟨-c, 1, by rw [hc]; ring⟩
    simpa [show (8 : ℤ) = 2 ^ 3 by norm_num] using h2m.pow_left (m := 3)
  have : (8 : ℤ) * m ∣ D := hcop8.mul_dvd h8D hmD
  push_cast
  exact this

/-! Controls: `RADvd` is FALSE at `N = 76` (the paper's isosceles-(α+β) instance `(90,19,100)` on `(380,380,342)`),
at `N = 60` (`(7,8)`, tile `(56,15,64)`), and at every `N` with an odd square factor (e.g. `N = 18`: `(e,f,K) = (1,3,6)`). -/
theorem not_radvd_76 : ¬ RADvd 76 := by
  intro h
  have := h 9 10 38 (by norm_num) (by norm_num) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num) (by norm_num)
  norm_num at this

theorem not_radvd_60 : ¬ RADvd 60 := by
  intro h
  have := h 7 8 30 (by norm_num) (by norm_num) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num) (by norm_num)
  norm_num at this

theorem not_radvd_18 : ¬ RADvd 18 := by
  intro h
  have := h 1 3 6 (by norm_num) (by norm_num) (by rw [Int.isCoprime_iff_gcd_eq_one]; decide) (by norm_num) (by norm_num)
  norm_num at this

theorem radvd_56 : RADvd 56 := by
  have := ra_dvd_of_eight 7 (by decide +kernel) (by norm_num)
  simpa using this

theorem radvd_152 : RADvd 152 := by
  have := ra_dvd_of_eight 19 (by decide +kernel) (by norm_num)
  simpa using this

end Erdos634.Draft.NSQRA

#print axioms Erdos634.Draft.NSQRA.ra_dvd_of_squarefree
#print axioms Erdos634.Draft.NSQRA.ra_dvd_of_eight
#print axioms Erdos634.Draft.NSQRA.not_radvd_76
#print axioms Erdos634.Draft.NSQRA.radvd_152
