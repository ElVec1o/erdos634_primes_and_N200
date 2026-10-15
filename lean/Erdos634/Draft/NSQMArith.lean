/-
Draft/NSQMArith.lean — Pure arithmetic of the refined S5 leaf (S5').
  S5pFree N : no t ≥ 2, coprime 0<e<f with N = t² (f²−e²).
  S5pChk N  : decidable closed form (no t ≥ 2, t² ∣ N, with N/t² odd ≥ 3 or ≡ 0 mod 8).      S5pChk ⇔ S5pFree.
  RADvdM N  : `N ∣ (f−e) K` for every (e,f,K,M) with N = K M, K ≡ M ≡ N (2), K (f−e) = M (f+e).
  s5pFree_imp_radvdM : S5pFree N → RADvdM N.      radvd_imp_s5pFree : (old) RADvd hypothesis ⇒ S5pFree.  No sorry, no native_decide.
-/
import Mathlib

namespace Erdos634.Draft.NSQM

def S5pFree (N : ℕ) : Prop :=
  ∀ t e f : ℤ, 2 ≤ t → 0 < e → e < f → IsCoprime e f → (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) → False

def RADvdM (N : ℕ) : Prop :=
  ∀ e f K M : ℤ, 0 < e → e < f → IsCoprime e f → 0 < K → 0 < M → (N : ℤ) = K * M →
    (2 : ℤ) ∣ K - N → (2 : ℤ) ∣ M - N → K * (f - e) = M * (f + e) → (N : ℤ) ∣ (f - e) * K

theorem not_both_even {e f : ℤ} (hcop : IsCoprime e f) (he : Even e) (hf : Even f) : False := by
  obtain ⟨a, b, hab⟩ := hcop
  obtain ⟨x, hx⟩ := he; obtain ⟨y, hy⟩ := hf
  have h2 : 2 * (a * x + b * y) = 1 := by rw [hx, hy] at hab; linarith
  omega

theorem s5pFree_imp_radvdM {N : ℕ} (h : S5pFree N) : RADvdM N := by
  intro e f K M he hef hcop hK hM hNKM hKp hMp hrel
  have hfe : f * (K - M) = e * (K + M) := by linarith
  have hdvd : f ∣ K + M := hcop.symm.dvd_of_dvd_mul_left ⟨K - M, by linarith⟩
  obtain ⟨u, hu⟩ := hdvd
  have hf0 : 0 < f := by omega
  have hKM : K - M = e * u := by
    have : f * (K - M) = f * (e * u) := by rw [hfe, hu]; ring
    exact mul_left_cancel₀ hf0.ne' this
  have hupos : 0 < u := by
    by_contra hle; push Not at hle
    nlinarith
  have hKMe : Even (K + M) := by
    obtain ⟨a, ha⟩ := hKp; obtain ⟨b, hb⟩ := hMp; exact ⟨a + b + N, by linarith⟩
  have hKMe' : Even (K - M) := by
    obtain ⟨a, ha⟩ := hKp; obtain ⟨b, hb⟩ := hMp; exact ⟨a - b, by linarith⟩
  have hue : Even u := by
    by_contra hodd
    have h1 : Even (f * u) := by rw [← hu]; exact hKMe
    have h2 : Even (e * u) := by rw [← hKM]; exact hKMe'
    rw [Int.even_mul] at h1 h2
    exact not_both_even hcop (h2.resolve_right hodd) (h1.resolve_right hodd)
  obtain ⟨t, ht⟩ := hue
  have htpos : 0 < t := by omega
  have hK' : K = (f + e) * t := by rw [ht] at hu hKM; linarith
  have hM' : M = (f - e) * t := by rw [ht] at hu hKM; linarith
  have hN : (N : ℤ) = t ^ 2 * (f ^ 2 - e ^ 2) := by rw [hNKM, hK', hM']; ring
  by_cases ht2 : 2 ≤ t
  · exact (h t e f ht2 he hef hcop hN).elim
  · have ht1 : t = 1 := by omega
    subst ht1
    exact ⟨1, by rw [hK']; rw [hN]; ring⟩

/-- (old hypothesis shape) any statement `N ∣ (f−e) K` for the pair `K = (f+e) t`, `M = (f−e) t` forces `t = 1`: hence
`RADvd`-type hypotheses imply `S5pFree`. -/
theorem s5pFree_of_dvd {N : ℕ} (hN0 : 0 < N)
    (hd : ∀ e f K : ℤ, 0 < e → e < f → IsCoprime e f → 0 < K → (N : ℤ) * (f + e) = K ^ 2 * (f - e) →
      (N : ℤ) ∣ (f - e) * K) : S5pFree N := by
  intro t e f ht he hef hcop hN
  have hK : 0 < (f + e) * t := by
    apply mul_pos <;> omega
  have hEq : (N : ℤ) * (f + e) = ((f + e) * t) ^ 2 * (f - e) := by rw [hN]; ring
  obtain ⟨c, hc⟩ := hd e f ((f + e) * t) he hef hcop hK hEq
  have h1 : (f - e) * ((f + e) * t) = t * (f ^ 2 - e ^ 2) := by ring
  have hpos : 0 < f ^ 2 - e ^ 2 := by nlinarith
  have hNpos : (0 : ℤ) < N := by exact_mod_cast hN0
  rw [h1, hN] at hc
  have h2 : t * (f ^ 2 - e ^ 2) = t * (f ^ 2 - e ^ 2) * (t * c) := by
    calc t * (f ^ 2 - e ^ 2) = t ^ 2 * (f ^ 2 - e ^ 2) * c := hc
      _ = _ := by ring
  have h3 : t * c = 1 := by
    have hne : t * (f ^ 2 - e ^ 2) ≠ 0 := by positivity
    have := mul_left_cancel₀ hne (by linarith : t * (f ^ 2 - e ^ 2) * 1 = t * (f ^ 2 - e ^ 2) * (t * c))
    exact this.symm
  by_cases hc1 : 1 ≤ c
  · nlinarith [h3, ht]
  · nlinarith [h3, ht]

/-! ## decidable closed form -/

def S5pChk (N : ℕ) : Prop :=
  ∀ t ≤ N, 2 ≤ t → t * t ∣ N →
    ¬ (N / (t * t) % 2 = 1 ∧ 3 ≤ N / (t * t)) ∧ ¬ (N / (t * t) % 8 = 0 ∧ 0 < N / (t * t))

instance (N : ℕ) : Decidable (S5pChk N) := by unfold S5pChk; infer_instance

theorem sq_mod8 (x : ℤ) (hx : x % 2 = 1) : x ^ 2 % 8 = 1 := by
  have : x % 8 = 1 ∨ x % 8 = 3 ∨ x % 8 = 5 ∨ x % 8 = 7 := by omega
  rcases this with h | h | h | h <;> simp [pow_two, Int.mul_emod, h]

theorem diff_sq_shape {e f : ℤ} (he : 0 < e) (hef : e < f) (hcop : IsCoprime e f) :
    ((f ^ 2 - e ^ 2) % 2 = 1 ∧ 3 ≤ f ^ 2 - e ^ 2) ∨ (f ^ 2 - e ^ 2) % 8 = 0 := by
  have hbig : 3 ≤ f ^ 2 - e ^ 2 := by nlinarith
  rcases Int.emod_two_eq_zero_or_one e with h0 | h1 <;> rcases Int.emod_two_eq_zero_or_one f with g0 | g1
  · exact (not_both_even hcop (Int.even_iff.mpr h0) (Int.even_iff.mpr g0)).elim
  · left; refine ⟨?_, hbig⟩
    obtain ⟨a, ha⟩ : ∃ a, e = 2 * a := ⟨e / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, f = 2 * b + 1 := ⟨f / 2, by omega⟩
    have : f ^ 2 - e ^ 2 = 2 * (2 * b ^ 2 + 2 * b - 2 * a ^ 2) + 1 := by rw [ha, hb]; ring
    omega
  · left; refine ⟨?_, hbig⟩
    obtain ⟨a, ha⟩ : ∃ a, e = 2 * a + 1 := ⟨e / 2, by omega⟩
    obtain ⟨b, hb⟩ : ∃ b, f = 2 * b := ⟨f / 2, by omega⟩
    have : f ^ 2 - e ^ 2 = 2 * (2 * b ^ 2 - 2 * a ^ 2 - 2 * a - 1) + 1 := by rw [ha, hb]; ring
    omega
  · right
    have h1 := sq_mod8 e h1
    have h2 := sq_mod8 f g1
    omega

theorem s5pFree_of_chk {N : ℕ} (h : S5pChk N) : S5pFree N := by
  intro t e f ht he hef hcop hN
  have hpos : 0 < f ^ 2 - e ^ 2 := by nlinarith
  lift t to ℕ using (by omega)
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (n : ℤ) = f ^ 2 - e ^ 2 := ⟨(f ^ 2 - e ^ 2).toNat, Int.toNat_of_nonneg hpos.le⟩
  have hNn : N = t * t * n := by
    have : (N : ℤ) = ((t * t * n : ℕ) : ℤ) := by push_cast; rw [hn, hN]; ring
    exact_mod_cast this
  have ht2 : 2 ≤ t := by exact_mod_cast ht
  have hn0 : 0 < n := by exact_mod_cast (hn ▸ hpos)
  have hdiv : N / (t * t) = n := by rw [hNn]; exact Nat.mul_div_cancel_left _ (by positivity)
  have htt : t * t ∣ N := ⟨n, hNn⟩
  have htN : t ≤ N := by
    have : t * t ≤ N := by rw [hNn]; exact Nat.le_mul_of_pos_right _ hn0
    nlinarith
  obtain ⟨c1, c2⟩ := h t htN ht2 htt
  rw [hdiv] at c1 c2
  rcases diff_sq_shape he hef hcop with ⟨h1, h3⟩ | h8
  · apply c1; constructor
    · have : (n : ℤ) % 2 = 1 := by rw [hn]; exact h1
      omega
    · have : (3 : ℤ) ≤ n := by rw [hn]; exact h3
      omega
  · apply c2; refine ⟨?_, hn0⟩
    have : (n : ℤ) % 8 = 0 := by rw [hn]; exact h8
    omega

theorem s5pChk_of_free {N : ℕ} (h : S5pFree N) : S5pChk N := by
  intro t htN ht2 htt
  obtain ⟨n, hn⟩ := htt
  have hdiv : N / (t * t) = n := by rw [hn]; exact Nat.mul_div_cancel_left _ (by positivity)
  rw [hdiv]
  have ht : (2 : ℤ) ≤ t := by exact_mod_cast ht2
  have hNZ : (N : ℤ) = (t : ℤ) ^ 2 * n := by rw [hn]; push_cast; ring
  constructor
  · rintro ⟨h1, h3⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    refine h t k (k + 1) ht (by omega) (by omega) ⟨-1, 1, by ring⟩ ?_
    rw [hNZ, hk]; push_cast; ring
  · rintro ⟨h8, h0⟩
    obtain ⟨k, hk⟩ : ∃ k : ℕ, n = 8 * k := ⟨n / 8, by omega⟩
    have hk1 : 1 ≤ k := by omega
    refine h t (2 * k - 1) (2 * k + 1) ht (by omega) (by omega) ⟨k, 1 - k, by ring⟩ ?_
    rw [hNZ, hk]; push_cast; ring

end Erdos634.Draft.NSQM

#print axioms Erdos634.Draft.NSQM.s5pFree_imp_radvdM
#print axioms Erdos634.Draft.NSQM.s5pFree_of_dvd
#print axioms Erdos634.Draft.NSQM.s5pFree_of_chk
#print axioms Erdos634.Draft.NSQM.s5pChk_of_free
