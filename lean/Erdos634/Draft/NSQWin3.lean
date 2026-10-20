/-
Draft/NSQWin3.lean -- third windowing step: the three remaining O(N) leaf loops of `CN'zETWD5` (`NSQWin2`), each with a soundness lemma for ALL `N`:
* `Pairs60W`, `Pairs120W`: the pair `(m, t)`, `m t = 3N`, is enumerated by its smaller member `t <= sqrt(3N)` (the pi/3 table has `t < m`;
  the 2pi/3 body is symmetric in `(s, t)`).
* `IsoH9bChkW`: divisors `e | N` enumerated as `d` and `N/d` with `d <= sqrt N`; the inner loop `b < e` is replaced by `k <= sqrt(N/2)`,
  `b = k^2/(N/e)` (from the second conjunct of `IsoBad`: `b (N/e) = k^2`, and `2b < e` gives `2 k^2 <= N`).
`CN'zETWD6 N -> CN'zETWD5 N` (`cnzETWD5_of_D6`).   Credit: Beeson-Rosu, Paliy, the S+ analysis.  UNAUDITED.  No sorry, no native_decide.
-/
import Erdos634.Draft.NSQWin2

set_option maxRecDepth 8000
set_option synthInstance.maxSize 20000
set_option synthInstance.maxHeartbeats 2000000

namespace Erdos634.Draft.NSQM
open Erdos634.Geometry Erdos634.Draft.AllNExclusion Erdos634.Draft.AllN3 Erdos634.Draft.NSQMain Erdos634.Draft.E60Irr

def Pairs60W (N : ℕ) : Prop :=
  ∀ t ≤ Nat.sqrt (3 * N), 1 ≤ t → t ∣ 3 * N → 3 * N / t ≤ N → t < 3 * N / t →
    (3 * N / t = N ∧ t = 3) ∨ ((3 * N / t) % 2 ≠ N % 2 ∨ t % 2 ≠ N % 2) ∨
    (16 * N ≤ (3 * N / t + t) ^ 2 → ¬ sqChk ((3 * N / t + t) ^ 2 - 16 * N))

instance (N : ℕ) : Decidable (Pairs60W N) := by unfold Pairs60W sqChk; infer_instance

theorem pairs60_of_W {N : ℕ} (h : Pairs60W N) : Pairs60ChkSq N [] := by
  intro m hm h1 hd hle hlt
  have hN : 0 < N := by omega
  obtain ⟨t, htd⟩ : ∃ t, t = 3 * N / m := ⟨_, rfl⟩
  have hmt : t * m = 3 * N := by rw [htd]; exact Nat.div_mul_cancel hd
  have ht0 : 1 ≤ t := by rw [htd]; exact Nat.div_pos (by omega) (by omega)
  have hdt : 3 * N / t = m := by rw [htd]; exact Nat.div_div_self hd (by omega)
  have htdv : t ∣ 3 * N := ⟨m, hmt.symm⟩
  rw [← htd] at hlt hle
  have hts : t ≤ Nat.sqrt (3 * N) := Nat.le_sqrt.mpr (by nlinarith)
  have := h t hts ht0 htdv (by rw [hdt]; exact hm) (by rw [hdt]; exact hlt)
  rw [hdt] at this
  rw [← htd]
  rcases this with h | h | h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · refine Or.inr (Or.inr (Or.inr ?_))
    exact h

def Pairs120W (N : ℕ) : Prop :=
  ∀ s ≤ Nat.sqrt (3 * N), 1 ≤ s → s ∣ 3 * N → 3 * N / s ≤ N →
    ¬ sqChk ((s + 3 * N / s) ^ 2 + 4 * N) ∧ ¬ (s + 3 * N / s ∣ 2 * N)

instance (N : ℕ) : Decidable (Pairs120W N) := by unfold Pairs120W sqChk; infer_instance

theorem pairs120_of_W {N : ℕ} (h : Pairs120W N) : Pairs120Chk N := by
  intro s hs h1 hd hle
  obtain ⟨t, htd⟩ : ∃ t, t = 3 * N / s := ⟨_, rfl⟩
  have hst : s * t = 3 * N := by rw [htd]; exact Nat.mul_div_cancel' hd
  have hN : 0 < N := by omega
  rw [← htd] at hle ⊢
  by_cases hc : s * s ≤ 3 * N
  · have := h s (Nat.le_sqrt.mpr hc) h1 hd (by rw [← htd]; exact hle)
    rw [← htd] at this; exact this
  · have ht1 : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h0 | h0
      · rw [h0] at hst; omega
      · exact h0
    have htt : t * t ≤ 3 * N := by
      by_contra hcon
      have : 3 * N < s * s := by omega
      nlinarith
    have htdv : t ∣ 3 * N := ⟨s, by rw [← hst]; ring⟩
    have hts : 3 * N / t = s := by rw [← hst]; exact Nat.mul_div_cancel s ht1
    have := h t (Nat.le_sqrt.mpr htt) ht1 htdv (by rw [hts]; exact hs)
    rw [hts] at this
    rw [add_comm t s] at this
    exact this

def IsoQ (N e : ℕ) : Prop :=
  e < N → 3 ≤ e → ∀ k ≤ Nat.sqrt (N / 2), N / e ∣ k * k → 0 < k * k / (N / e) → 2 * (k * k / (N / e)) < e →
    Nat.gcd (k * k / (N / e)) e = 1 → ¬ IsoBad N (e - 2 * (k * k / (N / e))) (k * k / (N / e))

instance (N e : ℕ) : Decidable (IsoQ N e) := by unfold IsoQ; infer_instance

def IsoH9bChkW (N : ℕ) : Prop :=
  ∀ d ≤ Nat.sqrt N, 0 < d → d ∣ N → IsoQ N d ∧ IsoQ N (N / d)

instance (N : ℕ) : Decidable (IsoH9bChkW N) := by unfold IsoH9bChkW; infer_instance

theorem isoQ_apply {N e : ℕ} (hQ : IsoQ N e) (he : e < N) (h3 : 3 ≤ e) (hd : e ∣ N) {b : ℕ} (hb0 : 0 < b)
    (h2b : 2 * b < e) (hg : Nat.gcd b e = 1) (hbad : IsoBad N (e - 2 * b) b) : False := by
  have hN : 0 < N := by omega
  have hE : e - 2 * b + 2 * b = e := by omega
  have hm0 : 0 < N / e := Nat.div_pos (by omega) (by omega)
  have hem : e * (N / e) = N := Nat.mul_div_cancel' hd
  have hbad' := hbad
  unfold IsoBad at hbad'
  rw [hE] at hbad'
  have h2 := hbad'.2.1
  obtain ⟨k, hk⟩ : ∃ k, k = Nat.sqrt (b * (N / e)) := ⟨_, rfl⟩
  rw [← hk] at h2
  have hbk : k * k / (N / e) = b := by rw [h2]; exact Nat.mul_div_cancel _ hm0
  have hks : k ≤ Nat.sqrt (N / 2) := by
    apply Nat.le_sqrt.mpr
    apply (Nat.le_div_iff_mul_le (by norm_num)).mpr
    have : (2 * b + 1) * (N / e) ≤ e * (N / e) := Nat.mul_le_mul_right _ h2b
    nlinarith
  have hdv : N / e ∣ k * k := ⟨b, by rw [h2]; ring⟩
  have := hQ he h3 k hks hdv (by rw [hbk]; exact hb0) (by rw [hbk]; exact h2b) (by rw [hbk]; exact hg)
  rw [hbk] at this
  exact this hbad

theorem isoH9bChk_of_W {N : ℕ} (h : IsoH9bChkW N) : IsoH9bChk N := by
  intro e he h3 hd b hb hb0 h2b hg hbad
  have hN : 0 < N := by omega
  have hQ : IsoQ N e := by
    by_cases hc : e * e ≤ N
    · exact (h e (Nat.le_sqrt.mpr hc) (by omega) hd).1
    · have hd0 : 0 < N / e := Nat.div_pos (by omega) (by omega)
      have hem : e * (N / e) = N := Nat.mul_div_cancel' hd
      have hdd : N / (N / e) = e := Nat.div_div_self hd (by omega)
      have hle : N / e * (N / e) ≤ N := by
        by_contra hcon
        have : N < N / e * (N / e) := by omega
        have h1 : N / e < e := by
          by_contra h1; push Not at h1
          have : e * e ≤ N := by nlinarith
          exact hc this
        nlinarith
      have := (h (N / e) (Nat.le_sqrt.mpr hle) hd0 (Nat.div_dvd_of_dvd hd)).2
      rwa [hdd] at this
  exact isoQ_apply hQ he h3 hd hb0 h2b hg hbad

def LeafEsqW (N : ℕ) : Prop := N % 4 = 2 ∨ (11 ≤ N ∧ Pairs60W N ∧ Pairs120W N)
instance (N : ℕ) : Decidable (LeafEsqW N) := by unfold LeafEsqW; infer_instance

def CN'zETWD6 (N : ℕ) : Prop :=
  NQChkW N ∧ (EllChk2 N ∨ AsqChk N) ∧ NSqChkSq N ∧ HArithChkSq N ∧
    (N % 2 = 1 ∨ (N % 2 = 0 ∧ NHSqChkSq N)) ∧ LeafEsqW N ∧ (N % 4 = 2 ∨ F1ChkParW N) ∧ S2ChkSq N ∧ S3ChkSq N ∧ IsoH9bChkW N ∧
    (NoF2ChkSq N ∧ NoF3zChkSq N ∧ NoF4zChkSq N) ∧ GammaChkDW N ∧ S1t2ChkW N ∧ RWChkT2W N ∧ S5wChkW N

instance (N : ℕ) : Decidable (CN'zETWD6 N) := by unfold CN'zETWD6; infer_instance

theorem cnzETWD5_of_D6 {N : ℕ} (h : CN'zETWD6 N) : CN'zETWD5 N := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, h7, h8, h9, isoH9bChk_of_W h10, h11, h12, h13, h14, h15⟩
  rcases h6 with h | ⟨h, ha, hb⟩
  · exact Or.inl h
  · exact Or.inr ⟨h, pairs60_of_W ha, pairs120_of_W hb⟩

theorem not_tile_of_conditionsNSQzETWD6 (N : ℕ) (h : CN'zETWD6 N) (D : CongruentDissection N) : False :=
  not_tile_of_conditionsNSQzETWD5 N (cnzETWD5_of_D6 h) D

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.not_tile_of_conditionsNSQzETWD6
